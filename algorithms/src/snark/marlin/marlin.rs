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
    fft::EvaluationDomain,
    polycommit::{Evaluations, LabeledCommitment, PCProof, PCRandomness, PCUniversalParams, PolynomialCommitment},
    snark::marlin::{
        ahp::{AHPError, AHPForR1CS, EvaluationsProvider},
        fiat_shamir::traits::FiatShamirRng,
        params::OptimizationType,
        prover::{ProverConstraintSystem, ProverMessage},
        CircuitProvingKey,
        CircuitVerifyingKey,
        MarlinError,
        MarlinMode,
        PreparedCircuitVerifyingKey,
        Proof,
        UniversalSRS,
    },
};
use itertools::Itertools;
use snarkvm_fields::{PrimeField, ToConstraintField};
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
#[derive(derivative::Derivative)]
#[derivative(Clone(bound = ""), Debug(bound = ""))]
pub struct MarlinSNARK<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
    Input: ToConstraintField<TargetField>,
>(#[doc(hidden)] PhantomData<(TargetField, BaseField, PC, FS, MM, Input)>);

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
    Input: ToConstraintField<TargetField>,
> MarlinSNARK<TargetField, BaseField, PC, FS, MM, Input>
{
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generates the universal proving and verifying keys for the argument system.
    pub fn universal_setup<R: RngCore>(
        max_degree: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<TargetField, BaseField, PC>, MarlinError> {
        let setup_time = start_timer!(|| { format!("Marlin::UniversalSetup with max_degree {}", max_degree,) });

        let srs = PC::setup(max_degree, rng).map_err(Into::into);
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
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<TargetField>, R: RngCore>(
        c: &C,
        rng: &mut R,
    ) -> Result<
        (CircuitProvingKey<TargetField, BaseField, PC, MM>, CircuitVerifyingKey<TargetField, BaseField, PC, MM>),
        MarlinError,
    > {
        let circuit = AHPForR1CS::<_, MM>::index(c)?;
        let srs = Self::universal_setup(circuit.max_degree(), rng)?;
        Self::circuit_setup(&srs, c)
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn circuit_setup<C: ConstraintSynthesizer<TargetField>>(
        universal_srs: &UniversalSRS<TargetField, BaseField, PC>,
        circuit: &C,
    ) -> Result<
        (CircuitProvingKey<TargetField, BaseField, PC, MM>, CircuitVerifyingKey<TargetField, BaseField, PC, MM>),
        MarlinError,
    > {
        let index_time = start_timer!(|| "Marlin::CircuitSetup");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::<_, MM>::index(circuit)?;
        if universal_srs.max_degree() < index.max_degree() {
            return Err(MarlinError::IndexTooLarge(universal_srs.max_degree(), index.max_degree()));
        }

        let coefficient_support = AHPForR1CS::<_, MM>::get_degree_bounds(&index.index_info);

        // Marlin only needs degree 2 random polynomials.
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = PC::trim(
            universal_srs,
            index.max_degree(),
            [index.constraint_domain_size()],
            supported_hiding_bound,
            Some(&coefficient_support),
        )?;

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (circuit_commitments, circuit_commitment_randomness): (_, _) =
            PC::commit(&committer_key, index.iter().map(Into::into), None)?;
        end_timer!(commit_time);

        let circuit_commitments = circuit_commitments.into_iter().map(|c| c.commitment().clone()).collect();
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
    pub fn prove<C: ConstraintSynthesizer<TargetField>, R: RngCore>(
        circuit_proving_key: &CircuitProvingKey<TargetField, BaseField, PC, MM>,
        circuit: &C,
        zk_rng: &mut R,
    ) -> Result<Proof<TargetField, BaseField, PC>, MarlinError> {
        Self::prove_with_terminator(circuit_proving_key, circuit, &AtomicBool::new(false), zk_rng)
    }

    fn terminate(terminator: &AtomicBool) -> Result<(), MarlinError> {
        if terminator.load(Ordering::Relaxed) { Err(MarlinError::Terminated) } else { Ok(()) }
    }

    /// Same as [`Self::prove`] with an added termination flag, `terminator`.
    pub fn prove_with_terminator<C: ConstraintSynthesizer<TargetField>, R: RngCore>(
        circuit_proving_key: &CircuitProvingKey<TargetField, BaseField, PC, MM>,
        circuit: &C,
        terminator: &AtomicBool,
        zk_rng: &mut R,
    ) -> Result<Proof<TargetField, BaseField, PC>, MarlinError> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // TODO: Add check that c is in the correct mode.

        Self::terminate(terminator)?;

        let prover_init_state = AHPForR1CS::<_, MM>::prover_init(&circuit_proving_key.circuit, circuit)?;
        let public_input = prover_init_state.public_input();
        let padded_public_input = prover_init_state.padded_public_input();

        let mut fs_rng = FS::new();
        fs_rng.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        fs_rng.absorb_native_field_elements(&circuit_proving_key.circuit_verifying_key.circuit_commitments);
        fs_rng.absorb_nonnative_field_elements(padded_public_input, OptimizationType::Weight);

        // --------------------------------------------------------------------
        // First round

        Self::terminate(terminator)?;
        let (prover_first_message, prover_first_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_first_round(prover_init_state, zk_rng)?;
        Self::terminate(terminator)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) =
            PC::commit(&circuit_proving_key.committer_key, prover_first_oracles.iter_for_commit(), Some(zk_rng))?;
        end_timer!(first_round_comm_time);

        Self::verifier_absorb_labeled(&first_commitments, &prover_first_message, &mut fs_rng);
        Self::terminate(terminator)?;

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            circuit_proving_key.circuit_verifying_key.circuit_info,
            &mut fs_rng,
        )?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        Self::terminate(terminator)?;
        let (prover_second_message, prover_second_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_second_round(&verifier_first_message, prover_state, zk_rng);
        Self::terminate(terminator)?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitments, second_commitment_randomnesses) = PC::commit_with_terminator(
            &circuit_proving_key.committer_key,
            prover_second_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(second_round_comm_time);

        Self::verifier_absorb_labeled(&second_commitments, &prover_second_message, &mut fs_rng);
        Self::terminate(terminator)?;

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        Self::terminate(terminator)?;

        let (prover_third_message, prover_third_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitments, third_commitment_randomnesses) = PC::commit_with_terminator(
            &circuit_proving_key.committer_key,
            prover_third_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        Self::verifier_absorb_labeled(&third_commitments, &prover_third_message, &mut fs_rng);

        let (verifier_third_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round

        Self::terminate(terminator)?;

        let (prover_fourth_message, prover_fourth_oracles) =
            AHPForR1CS::<_, MM>::prover_fourth_round(&verifier_third_msg, prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_commitments, fourth_commitment_randomnesses) = PC::commit_with_terminator(
            &circuit_proving_key.committer_key,
            prover_fourth_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(fourth_round_comm_time);

        Self::verifier_absorb_labeled(&fourth_commitments, &prover_fourth_message, &mut fs_rng);

        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        Self::terminate(terminator)?;

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = circuit_proving_key
            .circuit
            .iter() // 12 items
            .chain(prover_first_oracles.iter_for_open()) // 3 or 4 items
            .chain(prover_second_oracles.iter())// 2 items
            .chain(prover_third_oracles.iter())// 3 items
            .chain(prover_fourth_oracles.iter())// 1 item
            .collect();

        Self::terminate(terminator)?;

        // Sanity check, whose length should be updated if the underlying structs are updated.
        assert_eq!(polynomials.len(), AHPForR1CS::<TargetField, MM>::polynomial_labels().count());

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_commitments.iter().map(|p| p.commitment()).cloned().collect(),
            second_commitments.iter().map(|p| p.commitment()).cloned().collect(),
            third_commitments.iter().map(|p| p.commitment()).cloned().collect(),
            fourth_commitments.iter().map(|p| p.commitment()).cloned().collect(),
        ];
        Self::terminate(terminator)?;

        let indexer_polynomials = AHPForR1CS::<TargetField, MM>::indexer_polynomials();

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
        let commitment_randomnesses: Vec<PC::Randomness> = circuit_proving_key
            .circuit_commitment_randomness
            .clone()
            .into_iter()
            .chain(first_commitment_randomnesses)
            .chain(second_commitment_randomnesses)
            .chain(third_commitment_randomnesses)
            .chain(fourth_commitment_randomnesses)
            .collect();

        if !MM::ZK {
            let empty_randomness = PC::Randomness::empty();
            assert!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
        }

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state, &mut fs_rng);
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_input,
            &polynomials,
            &prover_third_message,
            &verifier_state,
        )?;

        Self::terminate(terminator)?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations_unsorted = Vec::new();
        for (label, (_point_name, point)) in &query_set {
            let lc =
                lc_s.iter().find(|lc| &lc.label == label).ok_or_else(|| AHPError::MissingEval(label.to_string()))?;
            let evaluation = polynomials.get_lc_eval(lc, *point)?;
            if !AHPForR1CS::<TargetField, MM>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations_unsorted.push((label.to_string(), evaluation));
            }
        }

        evaluations_unsorted.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations_unsorted.iter().map(|x| x.1).collect::<Vec<TargetField>>();
        end_timer!(eval_time);

        Self::terminate(terminator)?;

        fs_rng.absorb_nonnative_field_elements(&evaluations, OptimizationType::Weight);

        let num_open_challenges: usize = 7;

        let mut opening_challenges = Vec::new();
        opening_challenges.append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges)?);

        let opening_challenges_f = |i| opening_challenges[i as usize];

        let pc_proof = PC::open_combinations_individual_opening_challenges(
            &circuit_proving_key.committer_key,
            &lc_s,
            polynomials,
            &labeled_commitments,
            &query_set,
            &opening_challenges_f,
            &commitment_randomnesses,
        )?;

        Self::terminate(terminator)?;

        // Gather prover messages together.
        let prover_messages =
            vec![prover_first_message, prover_second_message, prover_third_message, prover_fourth_message];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        assert_eq!(proof.pc_proof.is_hiding(), MM::ZK);
        proof.print_size_info();
        end_timer!(prover_time);

        Ok(proof)
    }

    fn verifier_absorb_labeled(
        commitments: &[LabeledCommitment<PC::Commitment>],
        message: &ProverMessage<TargetField>,
        fs_rng: &mut FS,
    ) {
        let commitments: Vec<_> = commitments.iter().map(|c| c.commitment()).cloned().collect();
        Self::verifier_absorb(&commitments, message, fs_rng)
    }

    fn verifier_absorb(commitments: &[PC::Commitment], message: &ProverMessage<TargetField>, fs_rng: &mut FS) {
        fs_rng.absorb_native_field_elements(commitments);
        if !message.field_elements.is_empty() {
            fs_rng.absorb_nonnative_field_elements(&message.field_elements, OptimizationType::Weight);
        };
    }

    /// Verify that a proof for the constraint system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify(
        circuit_verifying_key: &CircuitVerifyingKey<TargetField, BaseField, PC, MM>,
        public_input: &[TargetField],
        proof: &Proof<TargetField, BaseField, PC>,
    ) -> Result<bool, MarlinError> {
        Self::verify_with_fs_parameters(circuit_verifying_key, &FS::sample_params(), public_input, proof)
    }

    /// Verify that a proof for the constraint system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify_with_fs_parameters(
        circuit_verifying_key: &CircuitVerifyingKey<TargetField, BaseField, PC, MM>,
        fs_parameters: &FS::Parameters,
        public_input: &[TargetField],
        proof: &Proof<TargetField, BaseField, PC>,
    ) -> Result<bool, MarlinError> {
        let verifier_time = start_timer!(|| "Marlin::Verify");
        let first_commitments = &proof.commitments[0];
        let second_commitments = &proof.commitments[1];
        let third_commitments = &proof.commitments[2];
        let fourth_commitments = &proof.commitments[3];
        let proof_has_correct_zk_mode = if MM::ZK {
            first_commitments.len() == 4 && proof.pc_proof.is_hiding()
        } else {
            first_commitments.len() == 3 && !proof.pc_proof.is_hiding()
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
            let input_domain = EvaluationDomain::<TargetField>::new(public_input.len() + 1).unwrap();

            if cfg!(debug_assertions) {
                println!("Number of given public inputs: {}", public_input.len());
                println!("Size of evaluation domain x: {}", input_domain.size());
            }

            let mut new_input = vec![TargetField::one()];
            new_input.extend_from_slice(public_input);
            new_input.resize(core::cmp::max(public_input.len(), input_domain.size()), TargetField::zero());
            new_input
        };
        let public_input = ProverConstraintSystem::unformat_public_input(&padded_public_input);

        if cfg!(debug_assertions) {
            println!("Number of padded public variables: {}", padded_public_input.len());
        }

        let mut fs_rng = FS::with_parameters(fs_parameters);

        fs_rng.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        fs_rng.absorb_native_field_elements(&circuit_verifying_key.circuit_commitments);
        fs_rng.absorb_nonnative_field_elements(&padded_public_input, OptimizationType::Weight);

        // --------------------------------------------------------------------
        // First round
        Self::verifier_absorb(first_commitments, &proof.prover_messages[0], &mut fs_rng);
        let (_, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_first_round(circuit_verifying_key.circuit_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        Self::verifier_absorb(second_commitments, &proof.prover_messages[1], &mut fs_rng);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        Self::verifier_absorb(third_commitments, &proof.prover_messages[2], &mut fs_rng);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round
        Self::verifier_absorb(fourth_commitments, &proof.prover_messages[3], &mut fs_rng);
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

        let polynomial_labels = AHPForR1CS::<TargetField, MM>::polynomial_labels();

        // Gather commitments in one vector.
        let commitments: Vec<_> = circuit_verifying_key
            .iter()
            .chain(first_commitments)
            .chain(second_commitments)
            .chain(third_commitments)
            .chain(fourth_commitments)
            .cloned()
            .zip_eq(polynomial_labels)
            .zip_eq(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state, &mut fs_rng);

        fs_rng.absorb_nonnative_field_elements(&proof.evaluations, OptimizationType::Weight);

        let mut evaluations = Evaluations::new();

        let mut evaluation_labels = Vec::<(String, TargetField)>::new();

        for (label, (_point_name, q)) in query_set.iter().cloned() {
            if AHPForR1CS::<TargetField, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_ref()) {
                evaluations.insert((label, q), TargetField::zero());
            } else {
                evaluation_labels.push((label, q));
            }
        }
        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip_eq(&proof.evaluations) {
            evaluations.insert(q, *eval);
        }

        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_input,
            &evaluations,
            &proof.prover_messages[2],
            &verifier_state,
        )?;

        let evaluations_are_correct = {
            let num_open_challenges: usize = 7;

            let opening_challenges = fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges)?;

            let opening_challenges_f = |i| opening_challenges[i as usize];

            PC::check_combinations_individual_opening_challenges(
                &circuit_verifying_key.verifier_key,
                &lc_s,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                &opening_challenges_f,
                &mut fs_rng,
            )?
        };

        if !evaluations_are_correct {
            #[cfg(debug_assertions)]
            eprintln!("PC::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " PC::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct & proof_has_correct_zk_mode
        ));
        Ok(evaluations_are_correct & proof_has_correct_zk_mode)
    }

    /// Verify that a proof for the constraint system defined by `C` asserts that
    /// all constraints are satisfied using the prepared verifying key.
    pub fn prepared_verify(
        prepared_vk: &PreparedCircuitVerifyingKey<TargetField, BaseField, PC, MM>,
        public_input: &[TargetField],
        proof: &Proof<TargetField, BaseField, PC>,
    ) -> Result<bool, MarlinError> {
        Self::verify(&prepared_vk.orig_vk, public_input, proof)
    }

    /// Verify that a proof for the constraint system defined by `C` asserts that
    /// all constraints are satisfied using the prepared verifying key.
    pub fn prepared_verify_with_fs_parameters(
        prepared_vk: &PreparedCircuitVerifyingKey<TargetField, BaseField, PC, MM>,
        fs_parameters: &FS::Parameters,
        public_input: &[TargetField],
        proof: &Proof<TargetField, BaseField, PC>,
    ) -> Result<bool, MarlinError> {
        Self::verify_with_fs_parameters(&prepared_vk.orig_vk, fs_parameters, public_input, proof)
    }
}
