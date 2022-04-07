// Copyright (C) 2019-2022 Aleo Systems Inc.
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
    fft::EvaluationDomain,
    polycommit::sonic_pc::{Commitment, Evaluations, LabeledCommitment, Randomness, SonicKZG10},
    snark::marlin::{
        ahp::{AHPError, AHPForR1CS, EvaluationsProvider},
        fiat_shamir::traits::FiatShamirRng,
        params::OptimizationType,
        proof,
        prover,
        CircuitProvingKey,
        CircuitVerifyingKey,
        Commitments,
        MarlinError,
        MarlinMode,
        PreparedCircuitVerifyingKey,
        Proof,
        UniversalSRS,
    },
};
use itertools::Itertools;
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{One, ToConstraintField, Zero};
use snarkvm_r1cs::ConstraintSynthesizer;
use snarkvm_utilities::{to_bytes_le, ToBytes};

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicBool, Ordering},
};
use rand_core::RngCore;

/// The Marlin proof system.
#[derive(Clone, Debug)]
pub struct MarlinSNARK<
    E: PairingEngine,
    FS: FiatShamirRng<E::Fr, E::Fq>,
    MM: MarlinMode,
    Input: ToConstraintField<E::Fr>,
>(#[doc(hidden)] PhantomData<(E, FS, MM, Input)>);

impl<E: PairingEngine, FS: FiatShamirRng<E::Fr, E::Fq>, MM: MarlinMode, Input: ToConstraintField<E::Fr>>
    MarlinSNARK<E, FS, MM, Input>
{
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generates the universal proving and verifying keys for the argument system.
    pub fn universal_setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<UniversalSRS<E>, MarlinError> {
        let setup_time = start_timer!(|| { format!("Marlin::UniversalSetup with max_degree {}", max_degree,) });

        let srs = SonicKZG10::<E, FS>::setup(max_degree, rng).map_err(Into::into);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a trusted setup.
    ///
    /// # Warning
    ///
    /// This method should be used *only* for testing purposes, and not in production.
    /// In production, one should instead perform a universal setup via [`Self::universal_setup`],
    /// and then deterministically specialize the resulting universal SRS via [`Self::circuit_setup`].
    #[allow(clippy::type_complexity)]
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<E::Fr>, R: RngCore>(
        c: &C,
        rng: &mut R,
    ) -> Result<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E, MM>), MarlinError> {
        let circuit = AHPForR1CS::<_, MM>::index(c)?;
        let srs = Self::universal_setup(circuit.max_degree(), rng)?;
        Self::circuit_setup(&srs, c)
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &UniversalSRS<E>,
        circuit: &C,
    ) -> Result<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E, MM>), MarlinError> {
        let index_time = start_timer!(|| "Marlin::CircuitSetup");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::<_, MM>::index(circuit)?;
        if universal_srs.max_degree() < index.max_degree() {
            universal_srs
                .increase_degree(index.max_degree())
                .map_err(|_| MarlinError::IndexTooLarge(universal_srs.max_degree(), index.max_degree()))?;
        }

        let coefficient_support = AHPForR1CS::<_, MM>::get_degree_bounds(&index.index_info);

        // Marlin only needs degree 2 random polynomials.
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = SonicKZG10::<E, FS>::trim(
            universal_srs,
            index.max_degree(),
            [index.constraint_domain_size()],
            supported_hiding_bound,
            Some(&coefficient_support),
        )?;

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (circuit_commitments, circuit_commitment_randomness): (_, _) =
            SonicKZG10::<E, FS>::commit(&committer_key, index.iter().map(Into::into), None)?;
        end_timer!(commit_time);

        let circuit_commitments = circuit_commitments.into_iter().map(|c| *c.commitment()).collect();
        let circuit_verifying_key = CircuitVerifyingKey {
            circuit_info: index.index_info,
            circuit_commitments,
            verifier_key,
            mode: PhantomData,
        };

        let circuit_proving_key = CircuitProvingKey {
            circuit: index,
            circuit_commitment_randomness,
            circuit_verifying_key: circuit_verifying_key.clone(),
            committer_key,
        };

        end_timer!(index_time);

        Ok((circuit_proving_key, circuit_verifying_key))
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<E::Fr>, R: RngCore>(
        circuit_proving_key: &CircuitProvingKey<E, MM>,
        circuit: &C,
        zk_rng: &mut R,
    ) -> Result<Proof<E>, MarlinError> {
        Self::prove_with_terminator(circuit_proving_key, circuit, &AtomicBool::new(false), zk_rng)
    }

    fn terminate(terminator: &AtomicBool) -> Result<(), MarlinError> {
        if terminator.load(Ordering::Relaxed) { Err(MarlinError::Terminated) } else { Ok(()) }
    }

    /// Same as [`Self::prove`] with an added termination flag, `terminator`.
    pub fn prove_with_terminator<C: ConstraintSynthesizer<E::Fr>, R: RngCore>(
        circuit_proving_key: &CircuitProvingKey<E, MM>,
        circuit: &C,
        terminator: &AtomicBool,
        zk_rng: &mut R,
    ) -> Result<Proof<E>, MarlinError> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // TODO: Add check that c is in the correct mode.

        Self::terminate(terminator)?;

        let prover_init_state = AHPForR1CS::<_, MM>::init_prover(&circuit_proving_key.circuit, circuit)?;
        let public_input = prover_init_state.public_input();
        let padded_public_input = prover_init_state.padded_public_input();

        let mut fs_rng = FS::new();
        fs_rng.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        fs_rng.absorb_native_field_elements(&circuit_proving_key.circuit_verifying_key.circuit_commitments);
        fs_rng.absorb_nonnative_field_elements(padded_public_input.to_vec(), OptimizationType::Weight);

        // --------------------------------------------------------------------
        // First round

        Self::terminate(terminator)?;
        let (first_oracles, prover_state) = AHPForR1CS::<_, MM>::prover_first_round(prover_init_state, zk_rng)?;
        Self::terminate(terminator)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            &circuit_proving_key.committer_key,
            first_oracles.iter_for_commit(),
            Some(zk_rng),
        )?;
        end_timer!(first_round_comm_time);

        Self::verifier_absorb_labeled(&first_commitments, &mut fs_rng);
        Self::terminate(terminator)?;

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            circuit_proving_key.circuit_verifying_key.circuit_info,
            &mut fs_rng,
        )?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        Self::terminate(terminator)?;
        let (second_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_second_round(&verifier_first_message, prover_state, zk_rng);
        Self::terminate(terminator)?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitments, second_commitment_randomnesses) = SonicKZG10::<E, FS>::commit_with_terminator(
            &circuit_proving_key.committer_key,
            second_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(second_round_comm_time);

        Self::verifier_absorb_labeled(&second_commitments, &mut fs_rng);
        Self::terminate(terminator)?;

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        Self::terminate(terminator)?;

        let (prover_third_message, third_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitments, third_commitment_randomnesses) = SonicKZG10::<E, FS>::commit_with_terminator(
            &circuit_proving_key.committer_key,
            third_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        Self::verifier_absorb_labeled_with_msg(&third_commitments, &prover_third_message, &mut fs_rng);

        let (verifier_third_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round

        Self::terminate(terminator)?;

        let fourth_oracles = AHPForR1CS::<_, MM>::prover_fourth_round(&verifier_third_msg, prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_commitments, fourth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit_with_terminator(
            &circuit_proving_key.committer_key,
            fourth_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(fourth_round_comm_time);

        Self::verifier_absorb_labeled(&fourth_commitments, &mut fs_rng);

        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        Self::terminate(terminator)?;

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = circuit_proving_key
            .circuit
            .iter() // 12 items
            .chain(first_oracles.iter_for_open()) // 3 or 4 items
            .chain(second_oracles.iter())// 2 items
            .chain(third_oracles.iter())// 3 items
            .chain(fourth_oracles.iter())// 1 item
            .collect();

        Self::terminate(terminator)?;

        // Sanity check, whose length should be updated if the underlying structs are updated.
        assert_eq!(polynomials.len(), AHPForR1CS::<E::Fr, MM>::polynomial_labels().count());

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = Commitments {
            w: *first_commitments[0].commitment(),
            z_a: *first_commitments[1].commitment(),
            z_b: *first_commitments[2].commitment(),
            mask_poly: MM::ZK.then(||  *first_commitments[3].commitment()),

            g_1: *second_commitments[0].commitment(),
            h_1: *second_commitments[1].commitment(),


            g_a: *third_commitments[0].commitment(),
            g_b: *third_commitments[1].commitment(),
            g_c: *third_commitments[2].commitment(),

            h_2: *fourth_commitments[0].commitment(),
        };

        let indexer_polynomials = AHPForR1CS::<E::Fr, MM>::indexer_polynomials();

        let labeled_commitments: Vec<_> = circuit_proving_key
            .circuit_verifying_key
            .iter()
            .cloned()
            .zip_eq(indexer_polynomials)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_commitments.into_iter())
            .chain(second_commitments.into_iter())
            .chain(third_commitments.into_iter())
            .chain(fourth_commitments.into_iter())
            .collect();

        // Gather commitment randomness together.
        let commitment_randomnesses: Vec<Randomness<E>> = circuit_proving_key
            .circuit_commitment_randomness
            .clone()
            .into_iter()
            .chain(first_commitment_randomnesses)
            .chain(second_commitment_randomnesses)
            .chain(third_commitment_randomnesses)
            .chain(fourth_commitment_randomnesses)
            .collect();

        if !MM::ZK {
            let empty_randomness = Randomness::<E>::empty();
            assert!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
        }

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_input,
            &polynomials,
            &prover_third_message,
            &verifier_state,
        )?;

        Self::terminate(terminator)?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = std::collections::BTreeMap::new();
        for (label, (_, point)) in query_set.to_set() {
            if !AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_str()) {
                let lc = lc_s.get(&label).ok_or_else(|| AHPError::MissingEval(label.to_string()))?;
                let evaluation = polynomials.get_lc_eval(lc, point)?;
                evaluations.insert(label, evaluation);
            }
        }

        let evaluations = proof::Evaluations::from_map(&evaluations);
        end_timer!(eval_time);

        Self::terminate(terminator)?;

        fs_rng.absorb_nonnative_field_elements(evaluations.to_field_elements(), OptimizationType::Weight);

        let pc_proof = SonicKZG10::<E, FS>::open_combinations(
            &circuit_proving_key.committer_key,
            lc_s.values(),
            polynomials,
            &labeled_commitments,
            &query_set.to_set(),
            &commitment_randomnesses,
            &mut fs_rng,
        )?;

        Self::terminate(terminator)?;

        let proof = Proof::<E>::new(commitments, evaluations, prover_third_message, pc_proof);
        assert_eq!(proof.pc_proof.is_hiding(), MM::ZK);
        end_timer!(prover_time);

        Ok(proof)
    }

    fn verifier_absorb_labeled_with_msg(
        comms: &[LabeledCommitment<Commitment<E>>],
        message: &prover::ThirdMessage<E::Fr>,
        fs_rng: &mut FS,
    ) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::verifier_absorb_with_msg(&commitments, message, fs_rng)
    }

    fn verifier_absorb_labeled(comms: &[LabeledCommitment<Commitment<E>>], fs_rng: &mut FS) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::verifier_absorb(&commitments, fs_rng)
    }

    fn verifier_absorb(commitments: &[Commitment<E>], fs_rng: &mut FS) {
        fs_rng.absorb_native_field_elements(commitments);
    }

    fn verifier_absorb_with_msg(commitments: &[Commitment<E>], msg: &prover::ThirdMessage<E::Fr>, fs_rng: &mut FS) {
        Self::verifier_absorb(commitments, fs_rng);
        fs_rng.absorb_nonnative_field_elements([msg.sum_a, msg.sum_b, msg.sum_c], OptimizationType::Weight);
    }

    /// Verify that a proof for the constraint system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify(
        circuit_verifying_key: &CircuitVerifyingKey<E, MM>,
        public_input: &[E::Fr],
        proof: &Proof<E>,
    ) -> Result<bool, MarlinError> {
        let verifier_time = start_timer!(|| "Marlin::Verify");
        let comms = &proof.commitments;
        let first_commitments = if MM::ZK {
            vec![comms.w, comms.z_a, comms.z_b, comms.mask_poly.unwrap()]
        } else {
            vec![comms.w, comms.z_a, comms.z_b]
        };
        let second_commitments = [comms.g_1, comms.h_1];
        let third_commitments = [comms.g_a, comms.g_b, comms.g_c];
        let fourth_commitments = [comms.h_2];

        let proof_has_correct_zk_mode = if MM::ZK {
            proof.pc_proof.is_hiding() & comms.mask_poly.is_some()
        } else {
            !proof.pc_proof.is_hiding() & comms.mask_poly.is_none()
        };
        if !proof_has_correct_zk_mode {
            eprintln!(
                "Too many commitments in the first round ({}) or proof has incorrect hiding mode ({})",
                first_commitments.len(),
                proof.pc_proof.is_hiding()
            );
            return Ok(false);
        }

        let padded_public_input = {
            let input_domain = EvaluationDomain::<E::Fr>::new(public_input.len() + 1).unwrap();

            let mut new_input = vec![E::Fr::one()];
            new_input.extend_from_slice(public_input);
            new_input.resize(core::cmp::max(public_input.len(), input_domain.size()), E::Fr::zero());
            new_input
        };
        let public_input = prover::ConstraintSystem::unformat_public_input(&padded_public_input);

        if cfg!(debug_assertions) {
            println!("Number of padded public variables: {}", padded_public_input.len());
        }

        let mut fs_rng = FS::new();
        fs_rng.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        fs_rng.absorb_native_field_elements(&circuit_verifying_key.circuit_commitments);
        fs_rng.absorb_nonnative_field_elements(padded_public_input, OptimizationType::Weight);

        // --------------------------------------------------------------------
        // First round
        Self::verifier_absorb(&first_commitments, &mut fs_rng);
        let (_, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_first_round(circuit_verifying_key.circuit_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        Self::verifier_absorb(&second_commitments, &mut fs_rng);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        Self::verifier_absorb_with_msg(&third_commitments, &proof.msg, &mut fs_rng);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round
        Self::verifier_absorb(&fourth_commitments, &mut fs_rng);
        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = circuit_verifying_key.circuit_info;
        let degree_bounds = vec![None; circuit_verifying_key.circuit_commitments.len()]
            .into_iter()
            .chain(AHPForR1CS::<_, MM>::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::<_, MM>::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::<_, MM>::prover_third_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::<_, MM>::prover_fourth_round_degree_bounds(&index_info));

        let polynomial_labels = AHPForR1CS::<E::Fr, MM>::polynomial_labels();

        // Gather commitments in one vector.
        let commitments: Vec<_> = circuit_verifying_key
            .iter()
            .chain(&first_commitments)
            .chain(&second_commitments)
            .chain(&third_commitments)
            .chain(&fourth_commitments)
            .cloned()
            .zip_eq(polynomial_labels)
            .zip_eq(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);

        fs_rng.absorb_nonnative_field_elements(proof.evaluations.to_field_elements(), OptimizationType::Weight);

        let mut evaluations = Evaluations::new();

        for (label, (_point_name, q)) in query_set.to_set() {
            if AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_ref()) {
                evaluations.insert((label, q), E::Fr::zero());
            } else {
                let eval = proof.evaluations.get(&label).ok_or_else(|| AHPError::MissingEval(label.clone()))?;
                evaluations.insert((label, q), eval);
            }
        }

        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_input,
            &evaluations,
            &proof.msg,
            &verifier_state,
        )?;

        let evaluations_are_correct = SonicKZG10::<E, FS>::check_combinations(
            &circuit_verifying_key.verifier_key,
            lc_s.values(),
            &commitments,
            &query_set.to_set(),
            &evaluations,
            &proof.pc_proof,
            &mut fs_rng,
        )?;

        if !evaluations_are_correct {
            #[cfg(debug_assertions)]
            eprintln!("SonicKZG10::<E, FS>::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " SonicKZG10::<E, FS>::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct & proof_has_correct_zk_mode
        ));
        Ok(evaluations_are_correct & proof_has_correct_zk_mode)
    }

    /// Verify that a proof for the constraint system defined by `C` asserts that
    /// all constraints are satisfied using the prepared verifying key.
    pub fn prepared_verify(
        prepared_vk: &PreparedCircuitVerifyingKey<E, MM>,
        public_input: &[E::Fr],
        proof: &Proof<E>,
    ) -> Result<bool, MarlinError> {
        Self::verify(&prepared_vk.orig_vk, public_input, proof)
    }
}
