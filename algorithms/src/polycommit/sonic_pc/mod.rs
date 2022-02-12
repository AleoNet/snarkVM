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

use crate::{
    fft::DensePolynomial,
    polycommit::{
        kzg10,
        optional_rng::OptionalRng,
        BatchLCProof,
        Evaluations,
        LabeledCommitment,
        LabeledPolynomial,
        LinearCombination,
        PCCommitterKey,
        PCError,
        PCRandomness,
        PCUniversalParams,
        PolynomialCommitment,
        PolynomialWithBasis,
        QuerySet,
    },
};
use snarkvm_curves::traits::{AffineCurve, PairingCurve, PairingEngine, ProjectiveCurve};
use snarkvm_fields::{One, Zero};
use snarkvm_utilities::rand::UniformRand;

use core::{
    convert::TryInto,
    marker::PhantomData,
    ops::Mul,
    sync::atomic::{AtomicBool, Ordering},
};
use rand_core::{RngCore, SeedableRng};
use std::collections::{BTreeMap, BTreeSet};

mod data_structures;
pub use data_structures::*;

use super::LabeledPolynomialWithBasis;

/// Polynomial commitment based on [\[KZG10\]][kzg], with degree enforcement and
/// batching taken from [[MBKM19, “Sonic”]][sonic] (more precisely, their
/// counterparts in [[Gabizon19, “AuroraLight”]][al] that avoid negative G1 powers).
/// The (optional) hiding property of the commitment scheme follows the approach
/// described in [[CHMMVW20, “Marlin”]][marlin].
///
/// [kzg]: http://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf
/// [sonic]: https://eprint.iacr.org/2019/099
/// [al]: https://eprint.iacr.org/2019/601
/// [marlin]: https://eprint.iacr.org/2019/1047
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SonicKZG10<E: PairingEngine> {
    _engine: PhantomData<E>,
}

impl<E: PairingEngine> SonicKZG10<E> {
    /// MSM for `commitments` and `coeffs`
    fn combine_commitments<'a>(
        coeffs_and_comms: impl IntoIterator<Item = (E::Fr, &'a Commitment<E>)>,
    ) -> E::G1Projective {
        let mut combined_comm = E::G1Projective::zero();
        for (coeff, comm) in coeffs_and_comms {
            if coeff.is_one() {
                combined_comm.add_assign_mixed(&comm.0);
            } else {
                combined_comm += &comm.0.mul(coeff).into();
            }
        }
        combined_comm
    }

    fn normalize_commitments(commitments: Vec<E::G1Projective>) -> impl Iterator<Item = Commitment<E>> {
        let mut comms = Vec::with_capacity(commitments.len());
        for comm in commitments {
            comms.push(comm);
        }
        let comms = E::G1Projective::batch_normalization_into_affine(comms);
        comms.into_iter().map(|c| kzg10::Commitment(c))
    }
}

impl<E: PairingEngine> PolynomialCommitment<E::Fr, E::Fq> for SonicKZG10<E> {
    type BatchProof = Vec<Self::Proof>;
    type Commitment = Commitment<E>;
    type CommitterKey = CommitterKey<E>;
    type PreparedCommitment = PreparedCommitment<E>;
    type PreparedVerifierKey = PreparedVerifierKey<E>;
    type Proof = kzg10::Proof<E>;
    type Randomness = Randomness<E>;
    type UniversalParams = UniversalParams<E>;
    type VerifierKey = VerifierKey<E>;

    fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<Self::UniversalParams, PCError> {
        kzg10::KZG10::setup(max_degree, &kzg10::KZG10DegreeBoundsConfig::MARLIN, true, rng).map_err(Into::into)
    }

    fn trim(
        pp: &Self::UniversalParams,
        supported_degree: usize,
        supported_lagrange_sizes: impl IntoIterator<Item = usize>,
        supported_hiding_bound: usize,
        enforced_degree_bounds: Option<&[usize]>,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), PCError> {
        let trim_time = start_timer!(|| "Trimming public parameters");
        let max_degree = pp.max_degree();
        if supported_degree > max_degree {
            return Err(PCError::TrimmingDegreeTooLarge);
        }

        let enforced_degree_bounds = enforced_degree_bounds.map(|bounds| {
            let mut v = bounds.to_vec();
            v.sort_unstable();
            v.dedup();
            v
        });

        let (shifted_powers_of_beta_g, shifted_powers_of_beta_times_gamma_g) = if let Some(enforced_degree_bounds) =
            enforced_degree_bounds.as_ref()
        {
            if enforced_degree_bounds.is_empty() {
                (None, None)
            } else {
                let highest_enforced_degree_bound = *enforced_degree_bounds.last().unwrap();
                if highest_enforced_degree_bound > supported_degree {
                    return Err(PCError::UnsupportedDegreeBound(highest_enforced_degree_bound));
                }

                let lowest_shift_degree = max_degree - highest_enforced_degree_bound;

                let shifted_ck_time = start_timer!(|| format!(
                    "Constructing `shifted_powers_of_beta_g` of size {}",
                    max_degree - lowest_shift_degree + 1
                ));

                let shifted_powers_of_beta_g = pp.powers_of_beta_g[lowest_shift_degree..].to_vec();
                let mut shifted_powers_of_beta_times_gamma_g = BTreeMap::new();
                // Also add degree 0.
                let _max_gamma_g = pp.powers_of_beta_times_gamma_g.keys().last().unwrap();
                for degree_bound in enforced_degree_bounds {
                    let shift_degree = max_degree - degree_bound;
                    let mut powers_for_degree_bound = Vec::with_capacity((max_degree + 2).saturating_sub(shift_degree));
                    for i in 0..=supported_hiding_bound + 1 {
                        // We have an additional degree in `powers_of_beta_times_gamma_g` beyond `powers_of_beta_g`.
                        if shift_degree + i < max_degree + 2 {
                            powers_for_degree_bound.push(pp.powers_of_beta_times_gamma_g[&(shift_degree + i)]);
                        }
                    }
                    shifted_powers_of_beta_times_gamma_g.insert(*degree_bound, powers_for_degree_bound);
                }

                end_timer!(shifted_ck_time);

                (Some(shifted_powers_of_beta_g), Some(shifted_powers_of_beta_times_gamma_g))
            }
        } else {
            (None, None)
        };

        let powers_of_beta_g = pp.powers_of_beta_g[..=supported_degree].to_vec();
        let powers_of_beta_times_gamma_g =
            (0..=supported_hiding_bound + 1).map(|i| pp.powers_of_beta_times_gamma_g[&i]).collect();

        let mut lagrange_bases_at_beta_g = BTreeMap::new();
        for size in supported_lagrange_sizes {
            if !size.is_power_of_two() {
                return Err(PCError::LagrangeBasisSizeIsNotPowerOfTwo);
            }
            if size > pp.powers_of_beta_g.len() {
                return Err(PCError::LagrangeBasisSizeIsTooLarge);
            }
            let domain = crate::fft::EvaluationDomain::new(size).unwrap();
            let lagrange_basis_at_beta_g = pp.lagrange_basis(domain);
            assert!(lagrange_basis_at_beta_g.len().is_power_of_two());
            lagrange_bases_at_beta_g.insert(domain.size(), lagrange_basis_at_beta_g);
        }

        let ck = CommitterKey {
            powers_of_beta_g,
            lagrange_bases_at_beta_g,
            powers_of_beta_times_gamma_g,
            shifted_powers_of_beta_g,
            shifted_powers_of_beta_times_gamma_g,
            enforced_degree_bounds,
            max_degree,
        };

        let g = pp.powers_of_beta_g[0];
        let h = pp.h;
        let beta_h = pp.beta_h;
        let gamma_g = pp.powers_of_beta_times_gamma_g[&0];
        let prepared_h = pp.prepared_h.clone();
        let prepared_beta_h = pp.prepared_beta_h.clone();

        let degree_bounds_and_neg_powers_of_h = if pp.inverse_neg_powers_of_beta_h.is_empty() {
            None
        } else {
            Some(
                pp.inverse_neg_powers_of_beta_h
                    .iter()
                    .map(|(d, affine)| (*d, *affine))
                    .collect::<Vec<(usize, E::G2Affine)>>(),
            )
        };

        let degree_bounds_and_prepared_neg_powers_of_h =
            degree_bounds_and_neg_powers_of_h.as_ref().map(|degree_bounds_and_neg_powers_of_h| {
                degree_bounds_and_neg_powers_of_h
                    .iter()
                    .map(|(d, affine)| (*d, affine.prepare()))
                    .collect::<Vec<(usize, <E::G2Affine as PairingCurve>::Prepared)>>()
            });

        let kzg10_vk = kzg10::VerifierKey::<E> { g, gamma_g, h, beta_h, prepared_h, prepared_beta_h };

        let vk = VerifierKey {
            vk: kzg10_vk,
            degree_bounds_and_neg_powers_of_h,
            degree_bounds_and_prepared_neg_powers_of_h,
            supported_degree,
            max_degree,
        };

        end_timer!(trim_time);
        Ok((ck, vk))
    }

    /// Outputs a commitment to `polynomial`.
    #[allow(clippy::type_complexity)]
    fn commit_with_terminator<'a>(
        ck: &Self::CommitterKey,
        polynomials: impl IntoIterator<Item = LabeledPolynomialWithBasis<'a, E::Fr>>,
        terminator: &AtomicBool,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Vec<LabeledCommitment<Self::Commitment>>, Vec<Self::Randomness>), PCError> {
        let rng = &mut OptionalRng(rng);
        let commit_time = start_timer!(|| "Committing to polynomials");
        let mut labeled_comms: Vec<LabeledCommitment<Self::Commitment>> = Vec::new();
        let mut randomness: Vec<Self::Randomness> = Vec::new();

        let mut pool = snarkvm_utilities::ExecutionPool::<Result<_, _>>::new();
        for p in polynomials {
            if terminator.load(Ordering::Relaxed) {
                return Err(PCError::Terminated);
            }
            let seed = rng.0.as_mut().map(|r| {
                let mut seed = [0u8; 32];
                r.fill_bytes(&mut seed);
                seed
            });

            kzg10::KZG10::<E>::check_degrees_and_bounds(
                ck.supported_degree(),
                ck.max_degree,
                ck.enforced_degree_bounds.as_deref(),
                p.clone(),
            )?;
            let degree_bound = p.degree_bound();
            let hiding_bound = p.hiding_bound();
            let label = p.label().clone();

            pool.add_job(move || {
                let mut rng = seed.map(rand::rngs::StdRng::from_seed);
                let commit_time = start_timer!(|| format!(
                    "Polynomial {} of degree {}, degree bound {:?}, and hiding bound {:?}",
                    label,
                    p.degree(),
                    degree_bound,
                    hiding_bound,
                ));

                let (comm, rand) = p
                    .sum()
                    .map(move |p| {
                        let rng_ref = rng.as_mut().map(|s| s as _);
                        match p {
                            PolynomialWithBasis::Lagrange { evaluations } => {
                                let domain = crate::fft::EvaluationDomain::new(evaluations.evaluations.len()).unwrap();
                                let lagrange_basis = ck
                                    .lagrange_basis(domain)
                                    .ok_or(PCError::UnsupportedLagrangeBasisSize(domain.size()))?;
                                assert!(domain.size().is_power_of_two());
                                assert!(lagrange_basis.size().is_power_of_two());
                                kzg10::KZG10::commit_lagrange(
                                    &lagrange_basis,
                                    &evaluations.evaluations,
                                    hiding_bound,
                                    terminator,
                                    rng_ref,
                                )
                            }
                            PolynomialWithBasis::Monomial { polynomial, degree_bound } => {
                                let powers = if let Some(degree_bound) = degree_bound {
                                    ck.shifted_powers_of_beta_g(degree_bound).unwrap()
                                } else {
                                    ck.powers()
                                };

                                kzg10::KZG10::commit(&powers, &polynomial, hiding_bound, terminator, rng_ref)
                            }
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .reduce(|mut a, b| {
                        a.0 += (E::Fr::one(), &b.0);
                        a.1 += (E::Fr::one(), &b.1);
                        a
                    })
                    .unwrap();

                end_timer!(commit_time);
                Ok((LabeledCommitment::new(label.to_string(), comm, degree_bound), rand))
            });
        }
        let results: Vec<Result<_, _>> = pool.execute_all();
        for result in results {
            let (comm, rand) = result?;
            labeled_comms.push(comm);
            randomness.push(rand);
        }

        end_timer!(commit_time);
        Ok((labeled_comms, randomness))
    }

    fn open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        _commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: E::Fr,
        opening_challenge: E::Fr,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let mut combined_polynomial = DensePolynomial::zero();
        let mut combined_rand = kzg10::Randomness::empty();
        let mut curr_challenge = opening_challenge;

        for (polynomial, rand) in labeled_polynomials.into_iter().zip(rands) {
            let enforced_degree_bounds: Option<&[usize]> = ck.enforced_degree_bounds.as_deref();

            kzg10::KZG10::<E>::check_degrees_and_bounds(
                ck.supported_degree(),
                ck.max_degree,
                enforced_degree_bounds,
                polynomial,
            )?;

            combined_polynomial += (curr_challenge, polynomial.polynomial());
            combined_rand += (curr_challenge, rand);
            curr_challenge *= &opening_challenge;
        }

        let proof_time = start_timer!(|| "Creating proof for polynomials");
        let proof = kzg10::KZG10::open(&ck.powers(), &combined_polynomial, point, &combined_rand)?;
        end_timer!(proof_time);

        Ok(proof)
    }

    fn check<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: E::Fr,
        values: impl IntoIterator<Item = E::Fr>,
        proof: &Self::Proof,
        opening_challenge: E::Fr,
        _rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a,
    {
        let check_time = start_timer!(|| "Checking evaluations");
        let mut combined_comms: BTreeMap<Option<usize>, E::G1Projective> = BTreeMap::new();
        let mut combined_witness: E::G1Projective = E::G1Projective::zero();
        let mut combined_adjusted_witness: E::G1Projective = E::G1Projective::zero();

        Self::accumulate_elems(
            &mut combined_comms,
            &mut combined_witness,
            &mut combined_adjusted_witness,
            vk,
            commitments,
            point,
            values,
            proof,
            opening_challenge,
            None,
        );

        let res = Self::check_elems(combined_comms, combined_witness, combined_adjusted_witness, vk);
        end_timer!(check_time);
        res
    }

    fn batch_check<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<E::Fr>,
        values: &Evaluations<E::Fr>,
        proof: &Self::BatchProof,
        opening_challenge: E::Fr,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a,
    {
        let commitments: BTreeMap<_, _> = commitments.into_iter().map(|c| (c.label().to_owned(), c)).collect();
        let mut query_to_labels_map = BTreeMap::new();

        for (label, (point_name, point)) in query_set.iter() {
            let labels = query_to_labels_map.entry(point_name).or_insert((point, BTreeSet::new()));
            labels.1.insert(label);
        }

        assert_eq!(proof.len(), query_to_labels_map.len());

        let mut randomizer = E::Fr::one();

        let mut combined_comms: BTreeMap<Option<usize>, E::G1Projective> = BTreeMap::new();
        let mut combined_witness: E::G1Projective = E::G1Projective::zero();
        let mut combined_adjusted_witness: E::G1Projective = E::G1Projective::zero();

        for ((_query_name, (query, labels)), p) in query_to_labels_map.into_iter().zip(proof) {
            let mut comms_to_combine: Vec<&'_ LabeledCommitment<_>> = Vec::new();
            let mut values_to_combine = Vec::new();
            for label in labels.into_iter() {
                let commitment =
                    commitments.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                let v_i = values
                    .get(&(label.clone(), *query))
                    .ok_or(PCError::MissingEvaluation { label: label.to_string() })?;

                comms_to_combine.push(commitment);
                values_to_combine.push(*v_i);
            }

            Self::accumulate_elems(
                &mut combined_comms,
                &mut combined_witness,
                &mut combined_adjusted_witness,
                vk,
                comms_to_combine.into_iter(),
                *query,
                values_to_combine.into_iter(),
                p,
                opening_challenge,
                Some(randomizer),
            );

            randomizer = u128::rand(rng).into();
        }

        Self::check_elems(combined_comms, combined_witness, combined_adjusted_witness, vk)
    }

    fn open_combinations<'a>(
        ck: &Self::CommitterKey,
        lc_s: impl IntoIterator<Item = &'a LinearCombination<E::Fr>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<E::Fr>,
        opening_challenge: E::Fr,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<BatchLCProof<E::Fr, E::Fq, Self>, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let label_map = polynomials
            .into_iter()
            .zip(rands)
            .zip(commitments)
            .map(|((p, r), c)| (p.label(), (p, r, c)))
            .collect::<BTreeMap<_, _>>();

        let mut lc_polynomials = Vec::new();
        let mut lc_randomness = Vec::new();
        let mut lc_commitments = Vec::new();
        let mut lc_info = Vec::new();

        for lc in lc_s {
            let lc_label = lc.label().clone();
            let mut poly = DensePolynomial::zero();
            let mut degree_bound = None;
            let mut hiding_bound = None;
            let mut randomness = Self::Randomness::empty();
            let mut comm = E::G1Projective::zero();

            let num_polys = lc.len();
            for (coeff, label) in lc.iter().filter(|(_, l)| !l.is_one()) {
                let label: &String = label.try_into().expect("cannot be one!");
                let &(cur_poly, cur_rand, curr_comm) =
                    label_map.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                if num_polys == 1 && cur_poly.degree_bound().is_some() {
                    assert!(coeff.is_one(), "Coefficient must be one for degree-bounded equations");
                    degree_bound = cur_poly.degree_bound();
                } else if cur_poly.degree_bound().is_some() {
                    eprintln!("Degree bound when number of equations is non-zero");
                    return Err(PCError::EquationHasDegreeBounds(lc_label));
                }

                // Some(_) > None, always.
                hiding_bound = core::cmp::max(hiding_bound, cur_poly.hiding_bound());
                poly += (*coeff, cur_poly.polynomial());
                randomness += (*coeff, cur_rand);
                comm += &curr_comm.commitment().0.into_projective().mul(*coeff);
            }

            let lc_poly = LabeledPolynomial::new(lc_label.clone(), poly, degree_bound, hiding_bound);
            lc_polynomials.push(lc_poly);
            lc_randomness.push(randomness);
            lc_commitments.push(comm);
            lc_info.push((lc_label, degree_bound));
        }

        let comms: Vec<Self::Commitment> = E::G1Projective::batch_normalization_into_affine(lc_commitments)
            .into_iter()
            .map(kzg10::Commitment::<E>)
            .collect();

        let lc_commitments = lc_info
            .into_iter()
            .zip(comms)
            .map(|((label, d), c)| LabeledCommitment::new(label, c, d))
            .collect::<Vec<_>>();

        let proof = Self::batch_open(
            ck,
            lc_polynomials.iter(),
            lc_commitments.iter(),
            query_set,
            opening_challenge,
            lc_randomness.iter(),
            rng,
        )?;
        Ok(BatchLCProof { proof, evaluations: None })
    }

    /// Checks that `values` are the true evaluations at `query_set` of the polynomials
    /// committed in `labeled_commitments`.
    fn check_combinations<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        lc_s: impl IntoIterator<Item = &'a LinearCombination<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<E::Fr>,
        evaluations: &Evaluations<E::Fr>,
        proof: &BatchLCProof<E::Fr, E::Fq, Self>,
        opening_challenge: E::Fr,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a,
    {
        let BatchLCProof { proof, .. } = proof;
        let label_comm_map = commitments.into_iter().map(|c| (c.label().to_owned(), c)).collect::<BTreeMap<_, _>>();

        let mut lc_commitments = Vec::new();
        let mut lc_info = Vec::new();
        let mut evaluations = evaluations.clone();
        for lc in lc_s {
            let lc_label = lc.label().clone();
            let num_polys = lc.len();

            let mut degree_bound = None;
            let mut combined_comm = E::G1Projective::zero();

            for (coeff, label) in lc.iter() {
                if label.is_one() {
                    for (&(ref label, _), ref mut eval) in evaluations.iter_mut() {
                        if label == &lc_label {
                            **eval -= coeff;
                        }
                    }
                } else {
                    let label: String = label.to_owned().try_into().unwrap();
                    let cur_comm =
                        label_comm_map.get(&label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                    if num_polys == 1 && cur_comm.degree_bound().is_some() {
                        assert!(coeff.is_one(), "Coefficient must be one for degree-bounded equations");
                        degree_bound = cur_comm.degree_bound();
                    } else if cur_comm.degree_bound().is_some() {
                        return Err(PCError::EquationHasDegreeBounds(lc_label));
                    }
                    combined_comm += &cur_comm.commitment().0.mul(*coeff).into();
                }
            }

            lc_commitments.push(combined_comm);
            lc_info.push((lc_label, degree_bound));
        }

        let comms = E::G1Projective::batch_normalization_into_affine(lc_commitments).into_iter().map(kzg10::Commitment);

        let lc_commitments: Vec<_> =
            lc_info.into_iter().zip(comms).map(|((label, d), c)| LabeledCommitment::new(label, c, d)).collect();

        Self::batch_check(vk, &lc_commitments, query_set, &evaluations, proof, opening_challenge, rng)
    }

    /// On input a list of polynomials, linear combinations of those polynomials,
    /// and a query set, `open_combination` outputs a proof of evaluation of
    /// the combinations at the points in the query set.
    fn open_combinations_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<E::Fr>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<E::Fr>,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
    ) -> Result<BatchLCProof<E::Fr, E::Fq, Self>, PCError>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let label_map = polynomials
            .into_iter()
            .zip(rands)
            .zip(commitments)
            .map(|((p, r), c)| (p.label(), (p, r, c)))
            .collect::<BTreeMap<_, _>>();

        let mut lc_polynomials = Vec::new();
        let mut lc_randomness = Vec::new();
        let mut lc_commitments = Vec::new();
        let mut lc_info = Vec::new();

        for lc in linear_combinations {
            let lc_label = lc.label().clone();
            let mut poly = DensePolynomial::zero();
            let mut degree_bound = None;
            let mut hiding_bound = None;

            let mut randomness = Self::Randomness::empty();
            let mut coeffs_and_comms = Vec::new();

            let num_polys = lc.len();
            for (coeff, label) in lc.iter().filter(|(_, l)| !l.is_one()) {
                let label: &String = label.try_into().expect("cannot be one!");
                let &(cur_poly, cur_rand, cur_comm) =
                    label_map.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;
                if num_polys == 1 && cur_poly.degree_bound().is_some() {
                    assert!(coeff.is_one(), "Coefficient must be one for degree-bounded equations");
                    degree_bound = cur_poly.degree_bound();
                } else if cur_poly.degree_bound().is_some() {
                    return Err(PCError::EquationHasDegreeBounds(lc_label));
                }
                // Some(_) > None, always.
                hiding_bound = core::cmp::max(hiding_bound, cur_poly.hiding_bound());
                poly += (*coeff, cur_poly.polynomial());
                randomness += (*coeff, cur_rand);
                coeffs_and_comms.push((*coeff, cur_comm.commitment()));
            }

            let lc_poly = LabeledPolynomial::new(lc_label.clone(), poly, degree_bound, hiding_bound);
            lc_polynomials.push(lc_poly);
            lc_randomness.push(randomness);
            lc_commitments.push(Self::combine_commitments(coeffs_and_comms));
            lc_info.push((lc_label, degree_bound));
        }

        let comms = Self::normalize_commitments(lc_commitments);
        let lc_commitments = lc_info
            .into_iter()
            .zip(comms)
            .map(|((label, d), c)| LabeledCommitment::new(label, c, d))
            .collect::<Vec<_>>();

        let proof = Self::batch_open_individual_opening_challenges(
            ck,
            lc_polynomials.iter(),
            lc_commitments.iter(),
            query_set,
            opening_challenges,
            lc_randomness.iter(),
        )?;

        Ok(BatchLCProof { proof, evaluations: None })
    }

    /// Check combinations with individual challenges.
    fn check_combinations_individual_opening_challenges<'a, R: RngCore>(
        vk: &Self::VerifierKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<E::Fr>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<E::Fr>,
        evaluations: &Evaluations<E::Fr>,
        proof: &BatchLCProof<E::Fr, E::Fq, Self>,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
        rng: &mut R,
    ) -> Result<bool, PCError>
    where
        Self::Commitment: 'a,
    {
        let BatchLCProof { proof, .. } = proof;
        let label_comm_map = commitments.into_iter().map(|c| (c.label(), c)).collect::<BTreeMap<_, _>>();

        let mut lc_commitments = Vec::new();
        let mut lc_info = Vec::new();
        let mut evaluations = evaluations.clone();

        let lc_processing_time = start_timer!(|| "Combining commitments");
        for lc in linear_combinations {
            let lc_label = lc.label().clone();
            let num_polys = lc.len();

            let mut degree_bound = None;
            let mut coeffs_and_comms = Vec::new();

            for (coeff, label) in lc.iter() {
                if label.is_one() {
                    for (&(ref label, _), ref mut eval) in evaluations.iter_mut() {
                        if label == &lc_label {
                            **eval -= coeff;
                        }
                    }
                } else {
                    let label: &String = label.try_into().unwrap();
                    let &cur_comm =
                        label_comm_map.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                    if num_polys == 1 && cur_comm.degree_bound().is_some() {
                        assert!(coeff.is_one(), "Coefficient must be one for degree-bounded equations");
                        degree_bound = cur_comm.degree_bound();
                    } else if cur_comm.degree_bound().is_some() {
                        return Err(PCError::EquationHasDegreeBounds(lc_label));
                    }
                    coeffs_and_comms.push((*coeff, cur_comm.commitment()));
                }
            }
            let lc_time = start_timer!(|| format!("Combining {} commitments for {}", num_polys, lc_label));
            lc_commitments.push(Self::combine_commitments(coeffs_and_comms));
            end_timer!(lc_time);
            lc_info.push((lc_label, degree_bound));
        }
        end_timer!(lc_processing_time);
        let combined_comms_norm_time = start_timer!(|| "Normalizing commitments");
        let comms = Self::normalize_commitments(lc_commitments);
        let lc_commitments = lc_info
            .into_iter()
            .zip(comms)
            .map(|((label, d), c)| LabeledCommitment::new(label, c, d))
            .collect::<Vec<_>>();
        end_timer!(combined_comms_norm_time);

        Self::batch_check_individual_opening_challenges(
            vk,
            &lc_commitments,
            query_set,
            &evaluations,
            proof,
            opening_challenges,
            rng,
        )
    }
}

impl<E: PairingEngine> SonicKZG10<E> {
    fn open_individual_opening_challenges<'a>(
        ck: &<Self as PolynomialCommitment<E::Fr, E::Fq>>::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        _commitments: impl IntoIterator<
            Item = &'a LabeledCommitment<<Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment>,
        >,
        point: &'a E::Fr,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
        rands: impl IntoIterator<Item = &'a <Self as PolynomialCommitment<E::Fr, E::Fq>>::Randomness>,
    ) -> Result<<Self as PolynomialCommitment<E::Fr, E::Fq>>::Proof, PCError>
    where
        <Self as PolynomialCommitment<E::Fr, E::Fq>>::Randomness: 'a,
        <Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment: 'a,
    {
        let mut combined_polynomial = DensePolynomial::zero();
        let mut combined_rand = kzg10::Randomness::empty();

        for (opening_challenge_counter, (polynomial, rand)) in labeled_polynomials.into_iter().zip(rands).enumerate() {
            let enforced_degree_bounds: Option<&[usize]> = ck.enforced_degree_bounds.as_deref();

            kzg10::KZG10::<E>::check_degrees_and_bounds(
                ck.supported_degree(),
                ck.max_degree,
                enforced_degree_bounds,
                polynomial,
            )?;

            let curr_challenge = opening_challenges(opening_challenge_counter as u64);
            combined_polynomial += (curr_challenge, polynomial.polynomial());
            combined_rand += (curr_challenge, rand);
        }

        let proof_time = start_timer!(|| "Creating proof for polynomials");
        let proof = kzg10::KZG10::open(&ck.powers(), &combined_polynomial, *point, &combined_rand)?;
        end_timer!(proof_time);

        Ok(proof)
    }

    /// On input a list of labeled polynomials and a query set, `open` outputs a proof of evaluation
    /// of the polynomials at the points in the query set.
    fn batch_open_individual_opening_challenges<'a>(
        ck: &<Self as PolynomialCommitment<E::Fr, E::Fq>>::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<E::Fr>>,
        commitments: impl IntoIterator<
            Item = &'a LabeledCommitment<<Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment>,
        >,
        query_set: &QuerySet<E::Fr>,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
        rands: impl IntoIterator<Item = &'a <Self as PolynomialCommitment<E::Fr, E::Fq>>::Randomness>,
    ) -> Result<<Self as PolynomialCommitment<E::Fr, E::Fq>>::BatchProof, PCError>
    where
        <Self as PolynomialCommitment<E::Fr, E::Fq>>::Randomness: 'a,
        <Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment: 'a,
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

        let mut proofs = Vec::new();
        for (_query_name, (query, labels)) in query_to_labels_map.into_iter() {
            let mut query_polys: Vec<&'a LabeledPolynomial<_>> = Vec::new();
            let mut query_rands: Vec<&'a <Self as PolynomialCommitment<E::Fr, E::Fq>>::Randomness> = Vec::new();
            let mut query_comms: Vec<&'a LabeledCommitment<<Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment>> =
                Vec::new();

            for label in labels {
                let (polynomial, rand, comm) =
                    poly_rand_comm.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                query_polys.push(polynomial);
                query_rands.push(rand);
                query_comms.push(comm);
            }

            let proof_time = start_timer!(|| "Creating proof");
            let proof = Self::open_individual_opening_challenges(
                ck,
                query_polys,
                query_comms,
                query,
                opening_challenges,
                query_rands,
            )?;

            end_timer!(proof_time);

            proofs.push(proof);
        }
        end_timer!(open_time);

        Ok(proofs)
    }

    /// Verifies that `value` is the evaluation at `x` of the polynomial
    /// committed inside `comm`.
    fn check_individual_opening_challenges<'a>(
        vk: &<Self as PolynomialCommitment<E::Fr, E::Fq>>::VerifierKey,
        commitments: impl IntoIterator<
            Item = &'a LabeledCommitment<<Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment>,
        >,
        point: &'a E::Fr,
        values: impl IntoIterator<Item = E::Fr>,
        proof: &<Self as PolynomialCommitment<E::Fr, E::Fq>>::Proof,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
    ) -> Result<bool, PCError>
    where
        <Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment: 'a,
    {
        let check_time = start_timer!(|| "Checking evaluations");
        let mut combined_comms: BTreeMap<Option<usize>, E::G1Projective> = BTreeMap::new();
        let mut combined_witness: E::G1Projective = E::G1Projective::zero();
        let mut combined_adjusted_witness: E::G1Projective = E::G1Projective::zero();

        Self::accumulate_elems_individual_opening_challenges(
            &mut combined_comms,
            &mut combined_witness,
            &mut combined_adjusted_witness,
            vk,
            commitments,
            *point,
            values,
            proof,
            opening_challenges,
            None,
        );

        let res = Self::check_elems(combined_comms, combined_witness, combined_adjusted_witness, vk);
        end_timer!(check_time);
        res
    }

    /// batch_check but with individual challenges
    fn batch_check_individual_opening_challenges<'a, R: RngCore>(
        vk: &<Self as PolynomialCommitment<E::Fr, E::Fq>>::VerifierKey,
        commitments: impl IntoIterator<
            Item = &'a LabeledCommitment<<Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment>,
        >,
        query_set: &QuerySet<E::Fr>,
        evaluations: &Evaluations<E::Fr>,
        proof: &<Self as PolynomialCommitment<E::Fr, E::Fq>>::BatchProof,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
        _rng: &mut R,
    ) -> Result<bool, PCError>
    where
        <Self as PolynomialCommitment<E::Fr, E::Fq>>::Commitment: 'a,
    {
        let commitments: BTreeMap<_, _> = commitments.into_iter().map(|c| (c.label(), c)).collect();

        let mut query_to_labels_map = BTreeMap::new();
        for (label, (point_name, point)) in query_set.iter() {
            let labels = query_to_labels_map.entry(point_name).or_insert((point, BTreeSet::new()));
            labels.1.insert(label);
        }

        // Implicit assumption: proofs are order in same manner as queries in
        // `query_to_labels_map`.
        let proofs: Vec<_> = proof.clone();
        assert_eq!(proofs.len(), query_to_labels_map.len());

        let mut result = true;
        for ((_point_name, (point, labels)), proof) in query_to_labels_map.into_iter().zip(proofs) {
            let mut comms: Vec<&'_ LabeledCommitment<_>> = Vec::new();
            let mut values = Vec::new();
            for label in labels {
                let commitment =
                    commitments.get(label).ok_or(PCError::MissingPolynomial { label: label.to_string() })?;

                let v_i = evaluations
                    .get(&(label.clone(), *point))
                    .ok_or(PCError::MissingEvaluation { label: label.to_string() })?;

                comms.push(commitment);
                values.push(*v_i);
            }

            let proof_time = start_timer!(|| "Checking per-query proof");
            result &= Self::check_individual_opening_challenges(vk, comms, point, values, &proof, opening_challenges)?;
            end_timer!(proof_time);
        }
        Ok(result)
    }
}

impl<E: PairingEngine> SonicKZG10<E> {
    #[allow(clippy::too_many_arguments)]
    fn accumulate_elems<'a>(
        combined_comms: &mut BTreeMap<Option<usize>, E::G1Projective>,
        combined_witness: &mut E::G1Projective,
        combined_adjusted_witness: &mut E::G1Projective,
        vk: &VerifierKey<E>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        point: E::Fr,
        values: impl IntoIterator<Item = E::Fr>,
        proof: &kzg10::Proof<E>,
        opening_challenge: E::Fr,
        randomizer: Option<E::Fr>,
    ) {
        let acc_time = start_timer!(|| "Accumulating elements");
        let mut curr_challenge = opening_challenge;

        // Keeps track of running combination of values
        let mut combined_values = E::Fr::zero();

        // Iterates through all of the commitments and accumulates common degree_bound elements in a BTreeMap
        for (labeled_comm, value) in commitments.into_iter().zip(values) {
            combined_values += &(value * curr_challenge);

            let comm = labeled_comm.commitment();
            let degree_bound = labeled_comm.degree_bound();

            // Applying opening challenge and randomness (used in batch_checking)
            let mut comm_with_challenge: E::G1Projective = comm.0.mul(curr_challenge).into();

            if let Some(randomizer) = randomizer {
                comm_with_challenge = comm_with_challenge.mul(randomizer);
            }

            // Accumulate values in the BTreeMap
            *combined_comms.entry(degree_bound).or_insert_with(E::G1Projective::zero) += &comm_with_challenge;
            curr_challenge *= &opening_challenge;
        }

        // Push expected results into list of elems. Power will be the negative of the expected power
        let mut witness: E::G1Projective = proof.w.into_projective();
        let mut adjusted_witness = vk.vk.g.mul(combined_values) - proof.w.mul(point);
        if let Some(random_v) = proof.random_v {
            adjusted_witness += &vk.vk.gamma_g.mul(random_v);
        }

        if let Some(randomizer) = randomizer {
            witness = witness.mul(randomizer);
            adjusted_witness = adjusted_witness.mul(randomizer);
        }

        *combined_witness += &witness;
        *combined_adjusted_witness += &adjusted_witness.into();
        end_timer!(acc_time);
    }

    fn accumulate_elems_individual_opening_challenges<'a>(
        combined_comms: &mut BTreeMap<Option<usize>, E::G1Projective>,
        combined_witness: &mut E::G1Projective,
        combined_adjusted_witness: &mut E::G1Projective,
        vk: &VerifierKey<E>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<E>>>,
        point: E::Fr,
        values: impl IntoIterator<Item = E::Fr>,
        proof: &kzg10::Proof<E>,
        opening_challenges: &dyn Fn(u64) -> E::Fr,
        randomizer: Option<E::Fr>,
    ) {
        let acc_time = start_timer!(|| "Accumulating elements");

        // Keeps track of running combination of values
        let mut combined_values = E::Fr::zero();

        // Iterates through all of the commitments and accumulates common degree_bound elements in a BTreeMap
        for (opening_challenge_counter, (labeled_commitment, value)) in commitments.into_iter().zip(values).enumerate()
        {
            let current_challenge = opening_challenges(opening_challenge_counter as u64);
            combined_values += &(value * current_challenge);

            let commitment = labeled_commitment.commitment();
            let degree_bound = labeled_commitment.degree_bound();

            // Applying opening challenge and randomness (used in batch_checking)
            let mut commitment_with_challenge: E::G1Projective = commitment.0.mul(current_challenge).into();

            if let Some(randomizer) = randomizer {
                commitment_with_challenge = commitment_with_challenge.mul(randomizer);
            }

            // Accumulate values in the BTreeMap
            *combined_comms.entry(degree_bound).or_insert_with(E::G1Projective::zero) += &commitment_with_challenge;
        }

        // Push expected results into list of elems. Power will be the negative of the expected power
        let mut witness: E::G1Projective = proof.w.into_projective();
        let mut adjusted_witness = vk.vk.g.mul(combined_values) - proof.w.mul(point);
        if let Some(random_v) = proof.random_v {
            adjusted_witness += &vk.vk.gamma_g.mul(random_v);
        }

        if let Some(randomizer) = randomizer {
            witness = proof.w.into_projective().mul(randomizer);
            adjusted_witness = adjusted_witness.mul(randomizer);
        }

        *combined_witness += &witness;
        *combined_adjusted_witness += &adjusted_witness.into();
        end_timer!(acc_time);
    }

    #[allow(clippy::type_complexity)]
    fn check_elems(
        combined_comms: BTreeMap<Option<usize>, E::G1Projective>,
        combined_witness: E::G1Projective,
        combined_adjusted_witness: E::G1Projective,
        vk: &VerifierKey<E>,
    ) -> Result<bool, PCError> {
        let check_time = start_timer!(|| "Checking elems");
        let mut g1_projective_elems = Vec::with_capacity(combined_comms.len() + 2);
        let mut g2_prepared_elems = Vec::with_capacity(combined_comms.len() + 2);

        for (degree_bound, comm) in combined_comms.into_iter() {
            let shift_power = if let Some(degree_bound) = degree_bound {
                vk.get_prepared_shift_power(degree_bound).ok_or(PCError::UnsupportedDegreeBound(degree_bound))?
            } else {
                vk.vk.prepared_h.clone()
            };

            g1_projective_elems.push(comm);
            g2_prepared_elems.push(shift_power);
        }

        g1_projective_elems.push(-combined_adjusted_witness);
        g2_prepared_elems.push(vk.vk.prepared_h.clone());

        g1_projective_elems.push(-combined_witness);
        g2_prepared_elems.push(vk.vk.prepared_beta_h.clone());

        let g1_prepared_elems_iter = E::G1Projective::batch_normalization_into_affine(g1_projective_elems)
            .into_iter()
            .map(|a| a.prepare())
            .collect::<Vec<_>>();

        let g1_g2_prepared = g1_prepared_elems_iter.iter().zip(g2_prepared_elems.iter());
        let is_one: bool = E::product_of_pairings(g1_g2_prepared).is_one();
        end_timer!(check_time);
        Ok(is_one)
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]

    use super::{CommitterKey, PolynomialCommitment, SonicKZG10};
    use crate::polycommit::test_templates::*;
    use snarkvm_curves::bls12_377::Bls12_377;
    use snarkvm_utilities::{rand::test_rng, FromBytes, ToBytes};

    use rand::distributions::Distribution;

    type PC<E> = SonicKZG10<E>;
    type PC_Bls12_377 = PC<Bls12_377>;

    #[test]
    fn test_committer_key_serialization() {
        let rng = &mut test_rng();
        let max_degree = rand::distributions::Uniform::from(8..=64).sample(rng);
        let supported_degree = rand::distributions::Uniform::from(1..=max_degree).sample(rng);

        let lagrange_size = |d: usize| if d.is_power_of_two() { d } else { d.next_power_of_two() >> 1 };

        let pp = PC_Bls12_377::setup(max_degree, rng).unwrap();

        let (ck, _vk) = PC_Bls12_377::trim(&pp, supported_degree, [lagrange_size(supported_degree)], 0, None).unwrap();

        let ck_bytes = ck.to_bytes_le().unwrap();
        let ck_recovered: CommitterKey<Bls12_377> = FromBytes::read_le(&ck_bytes[..]).unwrap();
        let ck_recovered_bytes = ck_recovered.to_bytes_le().unwrap();

        assert_eq!(&ck_bytes, &ck_recovered_bytes);
    }

    #[test]
    fn test_single_poly() {
        single_poly_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_quadratic_poly_degree_bound_multiple_queries() {
        quadratic_poly_degree_bound_multiple_queries_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_linear_poly_degree_bound() {
        linear_poly_degree_bound_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_single_poly_degree_bound() {
        single_poly_degree_bound_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_single_poly_degree_bound_multiple_queries() {
        single_poly_degree_bound_multiple_queries_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_two_polys_degree_bound_single_query() {
        two_polys_degree_bound_single_query_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
    }

    #[test]
    fn test_full_end_to_end() {
        full_end_to_end_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_single_equation() {
        single_equation_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_two_equation() {
        two_equation_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_two_equation_degree_bound() {
        two_equation_degree_bound_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_full_end_to_end_equation() {
        full_end_to_end_equation_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    #[should_panic]
    fn test_bad_degree_bound() {
        bad_degree_bound_test::<_, _, PC_Bls12_377>().expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }

    #[test]
    fn test_lagrange_commitment() {
        crate::polycommit::test_templates::lagrange_test_template::<_, _, PC_Bls12_377>()
            .expect("test failed for bls12-377");
        println!("Finished bls12-377");
    }
}
