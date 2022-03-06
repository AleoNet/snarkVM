// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

//! A crate for polynomial commitment schemes.
#![allow(clippy::module_inception)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

/// The core [\[KZG10\]][kzg] construction.
///
/// [kzg]: http://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
pub mod kzg10;

/// Polynomial commitment scheme based on the construction in [\[KZG10\]][kzg],
/// modified to obtain batching and to enforce strict
/// degree bounds by following the approach outlined in [[MBKM19,
/// “Sonic”]][sonic] (more precisely, via the variant in
/// [[Gabizon19, “AuroraLight”]][al] that avoids negative G1 powers).
///
/// [kzg]: http://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
/// [sonic]: https://eprint.iacr.org/2019/099
/// [al]: https://eprint.iacr.org/2019/601
/// [marlin]: https://eprint.iacr.org/2019/1047
pub mod sonic_pc;

/// Data structures used by a polynomial commitment scheme.
pub mod data_structures;
pub use data_structures::*;

/// Errors pertaining to query sets.
pub mod error;
pub use error::*;

/// A random number generator that bypasses some limitations of the Rust borrow
/// checker.
pub mod optional_rng;

#[cfg(test)]
pub mod test_templates;

use crate::Prepare;
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_utilities::{error as error_fn, serialize::*, FromBytes, ToBytes, ToMinimalBits};

use core::{fmt::Debug, sync::atomic::AtomicBool};
use rand_core::RngCore;
use std::collections::{BTreeMap, BTreeSet};

/// `QuerySet` is the set of queries that are to be made to a set of labeled polynomials/equations
/// `p` that have previously been committed to. Each element of a `QuerySet` is a `(label, query)`
/// pair, where `label` is the label of a polynomial in `p`, and `query` is the field element
/// that `p[label]` is to be queried at.
///
/// Added the third field: the point name.
pub type QuerySet<'a, T> = BTreeSet<(String, (String, T))>;

/// `Evaluations` is the result of querying a set of labeled polynomials or equations
/// `p` at a `QuerySet` `Q`. It maps each element of `Q` to the resulting evaluation.
/// That is, if `(label, query)` is an element of `Q`, then `evaluation.get((label, query))`
/// should equal `p[label].evaluate(query)`.
pub type Evaluations<'a, F> = BTreeMap<(String, F), F>;

/// A proof of satisfaction of linear combinations.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatchLCProof<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> {
    /// Evaluation proof.
    pub proof: PC::BatchProof,
    /// Evaluations required to verify the proof.
    pub evaluations: Option<Vec<F>>,
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> PCProof for BatchLCProof<F, CF, PC> {
    fn is_hiding(&self) -> bool {
        self.proof.is_hiding()
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> FromBytes for BatchLCProof<F, CF, PC> {
    fn read_le<R: Read>(mut reader: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut reader).map_err(|_| error_fn("could not deserialize struct"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> ToBytes for BatchLCProof<F, CF, PC> {
    fn write_le<W: Write>(&self, mut writer: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut writer).map_err(|_| error_fn("could not serialize struct"))
    }
}

/// Describes the interface for a polynomial commitment scheme that allows
/// a sender to commit to multiple polynomials and later provide a succinct proof
/// of evaluation for the corresponding commitments at a query set `Q`, while
/// enforcing per-polynomial degree bounds.
pub trait PolynomialCommitment<F: PrimeField, CF: PrimeField>: Sized + Clone + Debug + PartialEq + Eq {
    /// The universal parameters for the commitment scheme. These are "trimmed"
    /// down to `Self::CommitterKey` and `Self::VerifierKey` by `Self::trim`.
    type UniversalParams: PCUniversalParams + Clone;
    /// The committer key for the scheme; used to commit to a polynomial and then
    /// open the commitment to produce an evaluation proof.
    type CommitterKey: PCCommitterKey + ToBytes + FromBytes + Clone + Send + Sync;
    /// The verifier key for the scheme; used to check an evaluation proof.
    type VerifierKey: PCVerifierKey + Prepare<Self::PreparedVerifierKey> + ToConstraintField<CF> + Clone + Send + Sync;
    /// The prepared verifier key for the scheme; used to check an evaluation proof.
    type PreparedVerifierKey: Clone;
    /// The commitment to a polynomial.
    type Commitment: PCCommitment
        + Prepare<Self::PreparedCommitment>
        + ToConstraintField<CF>
        + ToMinimalBits
        + Clone
        + Debug
        + PartialEq
        + Eq
        + Send
        + Sync;
    /// The prepared commitment to a polynomial.
    type PreparedCommitment: Clone;
    /// The commitment randomness.
    type Randomness: PCRandomness + Clone + Send + Sync;
    /// The evaluation proof for a single point.
    type Proof: PCProof + Clone + Sync + Send;
    /// The evaluation proof for a query set.
    type BatchProof: CanonicalSerialize
        + CanonicalDeserialize
        + Clone
        + PCProof
        + From<Vec<Self::Proof>>
        + Into<Vec<Self::Proof>>
        + PartialEq
        + Eq
        + Debug
        + Send
        + Sync;

    /// Constructs public parameters when given as input the maximum degree `degree`
    /// for the polynomial commitment scheme.
    fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<Self::UniversalParams, PCError>;

    /// Specializes the public parameters for polynomials up to the given `supported_degree`
    /// and for enforcing degree bounds in the range `1..=supported_degree`.
    fn trim(
        parameters: &Self::UniversalParams,
        supported_degree: usize,
        supported_lagrange_sizes: impl IntoIterator<Item = usize>,
        supported_hiding_bound: usize,
        enforced_degree_bounds: Option<&[usize]>,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), PCError>;

    /// Outputs a commitments to `polynomials`. If `polynomials[i].is_hiding()`,
    /// then the `i`-th commitment is hiding up to `polynomials.hiding_bound()` queries.
    /// `rng` should not be `None` if `polynomials[i].is_hiding() == true` for any `i`.
    ///
    /// If for some `i`, `polynomials[i].is_hiding() == false`, then the
    /// corresponding randomness is `Self::Randomness::empty()`.
    ///
    /// If for some `i`, `polynomials[i].degree_bound().is_some()`, then that
    /// polynomial will have the corresponding degree bound enforced.
    #[allow(clippy::type_complexity)]
    fn commit<'a>(
        ck: &Self::CommitterKey,
        polynomials: impl IntoIterator<Item = LabeledPolynomialWithBasis<'a, F>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Vec<LabeledCommitment<Self::Commitment>>, Vec<Self::Randomness>), PCError> {
        Self::commit_with_terminator(ck, polynomials, &AtomicBool::new(false), rng)
    }

    /// Like [`Self::commit`] but with an added early termination signal.
    #[allow(clippy::type_complexity)]
    fn commit_with_terminator<'a>(
        ck: &Self::CommitterKey,
        polynomials: impl IntoIterator<Item = LabeledPolynomialWithBasis<'a, F>>,
        terminator: &AtomicBool,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Vec<LabeledCommitment<Self::Commitment>>, Vec<Self::Randomness>), PCError>;

    /// On input a list of labeled polynomials and a query point, `open` outputs a proof of evaluation
    /// of the polynomials at the query point.
    fn open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: F,
        opening_challenge: F,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a;

    /// On input a list of labeled polynomials and a query set, `open` outputs a proof of evaluation
    /// of the polynomials at the points in the query set.
    fn batch_open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        opening_challenge: F,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::BatchProof, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let poly_rand_comm: BTreeMap<_, _> = labeled_polynomials
            .into_iter()
            .zip(rands)
            .zip(commitments.into_iter())
            .map(|((poly, r), comm)| (poly.label(), (poly, r, comm)))
            .collect();

        let open_time = start_timer!(|| format!(
            "Opening {} polynomials at query set of size {}",
            poly_rand_comm.len(),
            query_set.len(),
        ));

        let mut query_to_labels_map = BTreeMap::new();

        for (label, (point_name, point)) in query_set.iter() {
            let labels = query_to_labels_map.entry(point_name).or_insert((point, BTreeSet::new()));
            labels.1.insert(label);
        }

        let mut pool = snarkvm_utilities::ExecutionPool::<Result<_, _>>::with_capacity(query_to_labels_map.len());
        for (_point_name, (&query, labels)) in query_to_labels_map.into_iter() {
            let mut query_polys = Vec::with_capacity(labels.len());
            let mut query_rands = Vec::with_capacity(labels.len());
            let mut query_comms = Vec::with_capacity(labels.len());

            for label in labels {
                let (polynomial, rand, comm) =
                    poly_rand_comm.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                query_polys.push(*polynomial);
                query_rands.push(*rand);
                query_comms.push(*comm);
            }

            pool.add_job(move || {
                let proof_time = start_timer!(|| "Creating proof");
                let proof = Self::open(ck, query_polys, query_comms, query, opening_challenge, query_rands, None);
                end_timer!(proof_time);
                proof
            });
        }
        end_timer!(open_time);
        let proofs: Vec<_> = pool.execute_all();
        let proofs = proofs.into_iter().collect::<Result<Vec<_>, _>>()?;

        Ok(proofs.into())
    }

    /// Verifies that `values` are the evaluations at `point` of the polynomials
    /// committed inside `commitments`.
    fn check<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: F,
        values: impl IntoIterator<Item = F>,
        proof: &Self::Proof,
        opening_challenge: F,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a;

    /// Checks that `values` are the true evaluations at `query_set` of the polynomials
    /// committed in `labeled_commitments`.
    fn batch_check<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        evaluations: &Evaluations<F>,
        proof: &Self::BatchProof,
        opening_challenge: F,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a,
    {
        let commitments: BTreeMap<_, _> = commitments.into_iter().map(|c| (c.label(), c)).collect();
        let mut query_to_labels_map = BTreeMap::new();
        for (label, (point_name, point)) in query_set.iter() {
            let labels = query_to_labels_map.entry(point_name).or_insert((point, BTreeSet::new()));
            labels.1.insert(label);
        }

        // Implicit assumption: proofs are order in same manner as queries in
        // `query_to_labels_map`.
        let proofs: Vec<_> = proof.clone().into();
        assert_eq!(proofs.len(), query_to_labels_map.len());

        let mut result = true;
        for ((_point_name, (query, labels)), proof) in query_to_labels_map.into_iter().zip(proofs) {
            let mut comms: Vec<&'_ LabeledCommitment<_>> = Vec::with_capacity(labels.len());
            let mut values = Vec::with_capacity(labels.len());
            for label in labels.into_iter() {
                let commitment =
                    commitments.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                let v_i = evaluations
                    .get(&(label.clone(), *query))
                    .ok_or(PCError::MissingEvaluation { label: label.to_string() })?;

                comms.push(commitment);
                values.push(*v_i);
            }

            let proof_time = start_timer!(|| "Checking per-query proof");
            result &= Self::check(vk, comms, *query, values, &proof, opening_challenge, rng)?;
            end_timer!(proof_time);
        }
        Ok(result)
    }

    /// On input a list of polynomials, linear combinations of those polynomials,
    /// and a query set, `open_combination` outputs a proof of evaluation of
    /// the combinations at the points in the query set.
    #[allow(clippy::too_many_arguments)]
    fn open_combinations<'a>(
        ck: &Self::CommitterKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        opening_challenge: F,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<BatchLCProof<F, CF, Self>, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let linear_combinations: Vec<_> = linear_combinations.into_iter().collect();
        let polynomials: Vec<_> = polynomials.into_iter().collect();
        let poly_query_set = lc_query_set_to_poly_query_set(linear_combinations.iter().copied(), query_set);
        let poly_evals = evaluate_query_set(polynomials.iter().copied(), &poly_query_set);
        let proof = Self::batch_open(ck, polynomials, commitments, &poly_query_set, opening_challenge, rands, rng)?;
        Ok(BatchLCProof { proof, evaluations: Some(poly_evals.values().copied().collect()) })
    }

    /// Checks that `evaluations` are the true evaluations at `query_set` of the
    /// linear combinations of polynomials committed in `commitments`.
    #[allow(clippy::too_many_arguments)]
    fn check_combinations<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        eqn_query_set: &QuerySet<F>,
        eqn_evaluations: &Evaluations<F>,
        proof: &BatchLCProof<F, CF, Self>,
        opening_challenge: F,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a,
    {
        let BatchLCProof { proof, evaluations: evals } = proof;

        let lc_s: BTreeMap<_, _> = linear_combinations.into_iter().map(|lc| (lc.label(), lc)).collect();

        let poly_query_set = lc_query_set_to_poly_query_set(lc_s.values().copied(), eqn_query_set);
        let poly_evals: Evaluations<_> =
            poly_query_set.iter().map(|(_, point)| point).cloned().zip(evals.clone().unwrap()).collect();

        for &(ref lc_label, (_, point)) in eqn_query_set {
            if let Some(lc) = lc_s.get(lc_label) {
                let claimed_rhs = *eqn_evaluations
                    .get(&(lc_label.clone(), point))
                    .ok_or(PCError::MissingEvaluation { label: lc_label.to_string() })?;

                let mut actual_rhs = F::zero();

                for (coeff, label) in lc.iter() {
                    let eval = match label {
                        LCTerm::One => F::one(),
                        LCTerm::PolyLabel(l) => *poly_evals
                            .get(&(l.clone(), point))
                            .ok_or(PCError::MissingEvaluation { label: l.clone() })?,
                    };

                    actual_rhs += &(*coeff * eval);
                }
                if claimed_rhs != actual_rhs {
                    eprintln!("Claimed evaluation of {} is incorrect", lc.label());
                    return Ok(false);
                }
            }
        }

        let pc_result =
            Self::batch_check(vk, commitments, &poly_query_set, &poly_evals, proof, opening_challenge, rng)?;
        if !pc_result {
            eprintln!("Evaluation proofs failed to verify");
            return Ok(false);
        }

        Ok(true)
    }

    /// On input a list of polynomials, linear combinations of those polynomials,
    /// and a query set, `open_combination` outputs a proof of evaluation of
    /// the combinations at the points in the query set.
    fn open_combinations_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        opening_challenges: &dyn Fn(u64) -> F,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
    ) -> Result<BatchLCProof<F, CF, Self>, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a;

    /// Check combinations with individual challenges.
    fn check_combinations_individual_opening_challenges<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        eqn_query_set: &QuerySet<F>,
        eqn_evaluations: &Evaluations<F>,
        proof: &BatchLCProof<F, CF, Self>,
        opening_challenges: &dyn Fn(u64) -> F,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a;
}

/// Evaluate the given polynomials at `query_set`.
pub fn evaluate_query_set<'a, F: PrimeField>(
    polys: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
    query_set: &QuerySet<'a, F>,
) -> Evaluations<'a, F> {
    let polys: BTreeMap<_, _> = polys.into_iter().map(|p| (p.label(), p)).collect();
    let mut evaluations = Evaluations::new();
    for (label, (_point_name, point)) in query_set {
        let poly = polys.get(label).expect("polynomial in evaluated lc is not found");
        let eval = poly.evaluate(*point);
        evaluations.insert((label.clone(), *point), eval);
    }
    evaluations
}

fn lc_query_set_to_poly_query_set<'a, F: 'a + PrimeField>(
    linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
    query_set: &QuerySet<F>,
) -> QuerySet<'a, F> {
    let mut poly_query_set = QuerySet::new();
    let lc_s = linear_combinations.into_iter().map(|lc| (lc.label(), lc));
    let linear_combinations: BTreeMap<_, _> = lc_s.collect();
    for (lc_label, (point_name, point)) in query_set {
        if let Some(lc) = linear_combinations.get(lc_label) {
            for (_, poly_label) in lc.iter().filter(|(_, l)| !l.is_one()) {
                if let LCTerm::PolyLabel(l) = poly_label {
                    poly_query_set.insert((l.into(), (point_name.clone(), *point)));
                }
            }
        }
    }
    poly_query_set
}
