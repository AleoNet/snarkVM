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
    ahp::{AHPError, AHPForR1CS, EvaluationsProvider},
    marlin::{CircuitProvingKey, CircuitVerifyingKey, FiatShamirRng, MarlinError, Proof, UniversalSRS},
};
use snarkvm_models::{curves::PrimeField, gadgets::r1cs::ConstraintSynthesizer};
use snarkvm_polycommit::{Evaluations, LabeledCommitment, PCUniversalParams, PolynomialCommitment};
use snarkvm_utilities::{bytes::ToBytes, rand::UniformRand, to_bytes};

use core::marker::PhantomData;
use digest::Digest;
use rand_core::RngCore;

/// The Marlin proof system.
pub struct MarlinSNARK<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest>(
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<D>,
);

impl<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest> MarlinSNARK<F, PC, D> {
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generates the universal proving and verifying keys for the argument system.
    pub fn universal_setup<R: RngCore>(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, MarlinError<PC::Error>> {
        let max_degree = AHPForR1CS::<F>::max_degree(num_constraints, num_variables, num_non_zero)?;
        let setup_time = start_timer!(|| {
            format!(
                "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
                max_degree, num_constraints, num_variables, num_non_zero,
            )
        });

        let srs = PC::setup(max_degree, rng).map_err(MarlinError::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn circuit_setup<C: ConstraintSynthesizer<F>>(
        universal_srs: &UniversalSRS<F, PC>,
        circuit: &C,
    ) -> Result<(CircuitProvingKey<F, PC>, CircuitVerifyingKey<F, PC>), MarlinError<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::CircuitSetup");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(circuit)?;
        if universal_srs.max_degree() < index.max_degree() {
            return Err(MarlinError::IndexTooLarge(
                universal_srs.max_degree(),
                index.max_degree(),
            ));
        }

        let coefficient_support = AHPForR1CS::get_degree_bounds(&index.index_info);
        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = PC::trim(
            &universal_srs,
            index.max_degree(),
            supported_hiding_bound,
            Some(&coefficient_support),
        )
        .map_err(MarlinError::from_pc_err)?;

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) =
            PC::commit(&committer_key, index.iter(), None).map_err(MarlinError::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms.into_iter().map(|c| c.commitment().clone()).collect();
        let circuit_verifying_key = CircuitVerifyingKey {
            circuit_info: index.index_info,
            circuit_commitments: index_comms,
            verifier_key,
        };

        let circuit_proving_key = CircuitProvingKey {
            circuit: index,
            circuit_commitment_randomness: index_comm_rands,
            circuit_verifying_key: circuit_verifying_key.clone(),
            committer_key,
        };

        end_timer!(index_time);

        Ok((circuit_proving_key, circuit_verifying_key))
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<F>, R: RngCore>(
        circuit_proving_key: &CircuitProvingKey<F, PC>,
        circuit: &C,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC>, MarlinError<PC::Error>> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // TODO: Add check that c is in the correct mode.

        let prover_init_state = AHPForR1CS::prover_init(&circuit_proving_key.circuit, circuit)?;
        let public_input = prover_init_state.public_input();
        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![
                &Self::PROTOCOL_NAME,
                &circuit_proving_key.circuit_verifying_key,
                &public_input
            ]
            .unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let (prover_first_message, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = PC::commit(
            &circuit_proving_key.committer_key,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(MarlinError::from_pc_err)?;
        end_timer!(first_round_comm_time);

        fs_rng.absorb(&to_bytes![first_comms, prover_first_message].unwrap());

        let (verifier_first_message, verifier_state) =
            AHPForR1CS::verifier_first_round(circuit_proving_key.circuit_verifying_key.circuit_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (prover_second_message, prover_second_oracles, prover_state) =
            AHPForR1CS::prover_second_round(&verifier_first_message, prover_state, zk_rng);

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitment, second_commitment_randomness) = PC::commit(
            &circuit_proving_key.committer_key,
            prover_second_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(MarlinError::from_pc_err)?;
        end_timer!(second_round_comm_time);

        fs_rng.absorb(&to_bytes![second_commitment, prover_second_message].unwrap());

        let (verifier_second_msg, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let (prover_third_message, prover_third_oracles) =
            AHPForR1CS::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitment, third_commitment_randomness) = PC::commit(
            &circuit_proving_key.committer_key,
            prover_third_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(MarlinError::from_pc_err)?;
        end_timer!(third_round_comm_time);

        fs_rng.absorb(&to_bytes![third_commitment, prover_third_message].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = circuit_proving_key
            .circuit
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
            let commitments = vec![
            first_comms.iter().map(|p| p.commitment()).cloned().collect(),
            second_commitment.iter().map(|p| p.commitment()).cloned().collect(),
            third_commitment.iter().map(|p| p.commitment()).cloned().collect(),
        ];
        let labeled_commitments: Vec<_> = circuit_proving_key
            .circuit_verifying_key
            .iter()
            .cloned()
            .zip(&AHPForR1CS::<F>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.into_iter())
            .chain(second_commitment.into_iter())
            .chain(third_commitment.into_iter())
            .collect();

        // Gather commitment randomness together.
        let commitment_randomnesses: Vec<PC::Randomness> = circuit_proving_key
            .circuit_commitment_randomness
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_commitment_randomness)
            .chain(third_commitment_randomness)
            .collect();

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);
        let lc_s = AHPForR1CS::construct_linear_combinations(&public_input, &polynomials, &verifier_state)?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = Vec::new();
        for (label, point) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or_else(|| AHPError::MissingEval(label.to_string()))?;
            let evaluation = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations.push(evaluation);
            }
        }
        end_timer!(eval_time);

        fs_rng.absorb(&evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let pc_proof = PC::open_combinations(
            &circuit_proving_key.committer_key,
            &lc_s,
            polynomials,
            &labeled_commitments,
            &query_set,
            opening_challenge,
            &commitment_randomnesses,
            Some(zk_rng),
        )
        .map_err(MarlinError::from_pc_err)?;

        // Gather prover messages together.
        let prover_messages = vec![prover_first_message, prover_second_message, prover_third_message];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        proof.print_size_info();
        end_timer!(prover_time);
        Ok(proof)
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify<R: RngCore>(
        circuit_verifying_key: &CircuitVerifyingKey<F, PC>,
        public_input: &[F],
        proof: &Proof<F, PC>,
        rng: &mut R,
    ) -> Result<bool, MarlinError<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin::Verify");

        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &circuit_verifying_key, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_first_round(circuit_verifying_key.circuit_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms, proof.prover_messages[2]].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = circuit_verifying_key.circuit_info;
        let degree_bounds = vec![None; circuit_verifying_key.circuit_commitments.len()]
            .into_iter()
            .chain(AHPForR1CS::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_third_round_degree_bounds(&index_info));

        // Gather commitments in one vector.
        let commitments = circuit_verifying_key
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(AHPForR1CS::<F>::polynomial_labels())
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d));

        let (query_set, verifier_state) = AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);

        fs_rng.absorb(&proof.evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let mut evaluations = Evaluations::new();
        let mut proof_evals = proof.evaluations.iter();
        for q in query_set.iter().cloned() {
            if AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&q.0.as_ref()) {
                evaluations.insert(q, F::zero());
            } else {
                evaluations.insert(q, *proof_evals.next().unwrap());
            }
        }

        let lc_s = AHPForR1CS::construct_linear_combinations(&public_input, &evaluations, &verifier_state)?;

        let evaluations_are_correct = PC::check_combinations(
            &circuit_verifying_key.verifier_key,
            &lc_s,
            commitments,
            &query_set,
            &evaluations,
            &proof.pc_proof,
            opening_challenge,
            rng,
        )
        .map_err(MarlinError::from_pc_err)?;

        if !evaluations_are_correct {
            eprintln!("PC::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " PC::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct
        ));
        Ok(evaluations_are_correct)
    }
}
