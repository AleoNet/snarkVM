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
    fiat_shamir::traits::FiatShamirRng,
    marlin::{CircuitProvingKey, CircuitVerifyingKey, MarlinError, MarlinMode, Proof, UniversalSRS},
    prover::ProverConstraintSystem,
    String,
    ToString,
    Vec,
};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::nonnative::params::OptimizationType;
use snarkvm_polycommit::{
    Evaluations,
    LabeledCommitment,
    LabeledPolynomial,
    PCProof,
    PCRandomness,
    PCUniversalParams,
    PolynomialCommitment,
};
use snarkvm_r1cs::{ConstraintSynthesizer, SynthesisError};
use snarkvm_utilities::{to_bytes_le, ToBytes};

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

use crate::marlin::PreparedCircuitVerifyingKey;
use core::{
    marker::PhantomData,
    sync::atomic::{AtomicBool, Ordering},
};
use rand_core::RngCore;

/// The Marlin proof system.
#[derive(Clone, Debug)]
pub struct MarlinSNARK<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
>(
    #[doc(hidden)] PhantomData<TargetField>,
    #[doc(hidden)] PhantomData<BaseField>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<FS>,
    #[doc(hidden)] PhantomData<MM>,
);

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
> MarlinSNARK<TargetField, BaseField, PC, FS, MM>
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
    #[allow(clippy::type_complexity)]
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<TargetField>, R: RngCore>(
        c: &C,
        rng: &mut R,
    ) -> Result<
        (
            CircuitProvingKey<TargetField, BaseField, PC, MM>,
            CircuitVerifyingKey<TargetField, BaseField, PC, MM>,
        ),
        MarlinError,
    > {
        let index_time = start_timer!(|| "Marlin::CircuitSpecificSetup");

        // TODO: Add check that c is in the correct mode.
        let circuit = AHPForR1CS::<_, MM>::index(c)?;
        let srs = PC::setup(circuit.max_degree(), rng)?;

        let coeff_support = AHPForR1CS::<_, MM>::get_degree_bounds(&circuit.index_info);

        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) =
            PC::trim(&srs, circuit.max_degree(), supported_hiding_bound, Some(&coeff_support))?;

        let mut vanishing_polys = vec![];
        if MM::RECURSION {
            let domain_h = EvaluationDomain::new(circuit.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = EvaluationDomain::new(circuit.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vanishing_polys = vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ];
        }

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (circuit_commitments, circuit_commitment_randomness): (_, _) =
            PC::commit(&committer_key, circuit.iter().chain(vanishing_polys.iter()), None)?;
        end_timer!(commit_time);

        let circuit_commitments = circuit_commitments
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();
        let index_vk = CircuitVerifyingKey {
            circuit_info: circuit.index_info,
            circuit_commitments,
            verifier_key,
            mode: PhantomData,
        };

        let index_pk = CircuitProvingKey {
            circuit,
            circuit_commitment_randomness,
            circuit_verifying_key: index_vk.clone(),
            committer_key,
        };

        end_timer!(index_time);

        Ok((index_pk, index_vk))
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn circuit_setup<C: ConstraintSynthesizer<TargetField>>(
        universal_srs: &UniversalSRS<TargetField, BaseField, PC>,
        circuit: &C,
    ) -> Result<
        (
            CircuitProvingKey<TargetField, BaseField, PC, MM>,
            CircuitVerifyingKey<TargetField, BaseField, PC, MM>,
        ),
        MarlinError,
    > {
        let index_time = start_timer!(|| "Marlin::CircuitSetup");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::<_, MM>::index(circuit)?;
        if universal_srs.max_degree() < index.max_degree() {
            return Err(MarlinError::IndexTooLarge(
                universal_srs.max_degree(),
                index.max_degree(),
            ));
        }

        let coefficient_support = AHPForR1CS::<_, MM>::get_degree_bounds(&index.index_info);

        // Marlin only needs degree 2 random polynomials.
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = PC::trim(
            &universal_srs,
            index.max_degree(),
            supported_hiding_bound,
            Some(&coefficient_support),
        )?;

        let mut vanishing_polynomials = vec![];
        if MM::RECURSION {
            let domain_h = EvaluationDomain::new(index.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k =
                EvaluationDomain::new(index.index_info.num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vanishing_polynomials = vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ];
        }

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (circuit_commitments, circuit_commitment_randomness): (_, _) =
            PC::commit(&committer_key, index.iter().chain(vanishing_polynomials.iter()), None)?;
        end_timer!(commit_time);

        let circuit_commitments = circuit_commitments
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();
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

    /// Same as [`prove`] with an added termination flag, [`terminator`].
    pub fn prove_with_terminator<C: ConstraintSynthesizer<TargetField>, R: RngCore>(
        circuit_proving_key: &CircuitProvingKey<TargetField, BaseField, PC, MM>,
        circuit: &C,
        terminator: &AtomicBool,
        zk_rng: &mut R,
    ) -> Result<Proof<TargetField, BaseField, PC>, MarlinError> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // TODO: Add check that c is in the correct mode.

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let prover_init_state = AHPForR1CS::<_, MM>::prover_init(&circuit_proving_key.circuit, circuit)?;
        let public_input = prover_init_state.public_input();
        let padded_public_input = prover_init_state.padded_public_input();

        let mut fs_rng = FS::new();

        if MM::RECURSION {
            fs_rng.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
            fs_rng.absorb_native_field_elements(&circuit_proving_key.circuit_verifying_key.circuit_commitments);
            fs_rng.absorb_nonnative_field_elements(&padded_public_input, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(
                &to_bytes_le![
                    &Self::PROTOCOL_NAME,
                    &circuit_proving_key.circuit_verifying_key,
                    padded_public_input
                ]
                .unwrap(),
            );
        }

        // --------------------------------------------------------------------
        // First round

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let (prover_first_message, prover_first_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_first_round(prover_init_state, zk_rng)?;

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) = PC::commit(
            &circuit_proving_key.committer_key,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )?;
        end_timer!(first_round_comm_time);

        if MM::RECURSION {
            fs_rng.absorb_native_field_elements(&first_commitments);
            if !prover_first_message.field_elements.is_empty() {
                fs_rng.absorb_nonnative_field_elements(&prover_first_message.field_elements, OptimizationType::Weight);
            }
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![first_commitments, prover_first_message].unwrap());
        }

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            circuit_proving_key.circuit_verifying_key.circuit_info,
            &mut fs_rng,
        )?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let (prover_second_message, prover_second_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_second_round(&verifier_first_message, prover_state, zk_rng);

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitments, second_commitment_randomnesses) = PC::commit_with_terminator(
            &circuit_proving_key.committer_key,
            prover_second_oracles.iter(),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(second_round_comm_time);

        if MM::RECURSION {
            fs_rng.absorb_native_field_elements(&second_commitments);
            if !prover_second_message.field_elements.is_empty() {
                fs_rng.absorb_nonnative_field_elements(&prover_second_message.field_elements, OptimizationType::Weight);
            }
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![second_commitments, prover_second_message].unwrap());
        }

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let (prover_third_message, prover_third_oracles) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitments, third_commitment_randomnesses) = PC::commit_with_terminator(
            &circuit_proving_key.committer_key,
            prover_third_oracles.iter(),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        if MM::RECURSION {
            fs_rng.absorb_native_field_elements(&third_commitments);
            if !prover_third_message.field_elements.is_empty() {
                fs_rng.absorb_nonnative_field_elements(&prover_third_message.field_elements, OptimizationType::Weight);
            }
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![third_commitments, prover_third_message].unwrap());
        }

        let verifier_state = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let vanishing_polys = if MM::RECURSION {
            let domain_h = EvaluationDomain::new(circuit_proving_key.circuit.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = EvaluationDomain::new(circuit_proving_key.circuit.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ]
        } else {
            vec![]
        };

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = circuit_proving_key
            .circuit
            .iter() // 12 items
            .chain(vanishing_polys.iter()) // 0 or 2 items
            .chain(prover_first_oracles.iter()) // 3 or 4 items
            .chain(prover_second_oracles.iter())// 3 items
            .chain(prover_third_oracles.iter())// 2 items
            .collect();

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        // Sanity check, whose length should be updated if the underlying structs are updated.
        assert_eq!(
            polynomials.len(),
            AHPForR1CS::<TargetField, MM>::polynomial_labels()
                .collect::<Vec<_>>()
                .len()
        );

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_commitments.iter().map(|p| p.commitment()).cloned().collect(),
            second_commitments.iter().map(|p| p.commitment()).cloned().collect(),
            third_commitments.iter().map(|p| p.commitment()).cloned().collect(),
        ];

        let indexer_polynomials = AHPForR1CS::<TargetField, MM>::indexer_polynomials();

        let labeled_commitments: Vec<_> = circuit_proving_key
            .circuit_verifying_key
            .iter()
            .cloned()
            .zip(indexer_polynomials)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_commitments.into_iter())
            .chain(second_commitments.into_iter())
            .chain(third_commitments.into_iter())
            .collect();

        // Gather commitment randomness together.
        let commitment_randomnesses: Vec<PC::Randomness> = circuit_proving_key
            .circuit_commitment_randomness
            .clone()
            .into_iter()
            .chain(first_commitment_randomnesses)
            .chain(second_commitment_randomnesses)
            .chain(third_commitment_randomnesses)
            .collect();

        if !MM::ZK {
            let empty_randomness = PC::Randomness::empty();
            assert!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
        }

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state, &mut fs_rng);
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(&public_input, &polynomials, &verifier_state)?;

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations_unsorted = Vec::new();
        for (label, (_point_name, point)) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or_else(|| AHPError::MissingEval(label.to_string()))?;
            let evaluation = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<TargetField, MM>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations_unsorted.push((label.to_string(), evaluation));
            }
        }

        evaluations_unsorted.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations_unsorted.iter().map(|x| x.1).collect::<Vec<TargetField>>();
        end_timer!(eval_time);

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        if MM::RECURSION {
            fs_rng.absorb_nonnative_field_elements(&evaluations, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![&evaluations].unwrap());
        }

        let pc_proof = if MM::RECURSION {
            let num_open_challenges: usize = 5;

            let mut opening_challenges = Vec::new();
            opening_challenges.append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges)?);

            let opening_challenges_f = |i| opening_challenges[i as usize];

            PC::open_combinations_individual_opening_challenges(
                &circuit_proving_key.committer_key,
                &lc_s,
                polynomials,
                &labeled_commitments,
                &query_set,
                &opening_challenges_f,
                &commitment_randomnesses,
            )?
        } else {
            let opening_challenge: TargetField = fs_rng.squeeze_128_bits_nonnative_field_elements(1)?[0];

            PC::open_combinations(
                &circuit_proving_key.committer_key,
                &lc_s,
                polynomials,
                &labeled_commitments,
                &query_set,
                opening_challenge,
                &commitment_randomnesses,
                Some(zk_rng),
            )?
        };

        if terminator.load(Ordering::Relaxed) {
            return Err(MarlinError::Terminated);
        }

        // Gather prover messages together.
        let prover_messages = vec![prover_first_message, prover_second_message, prover_third_message];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        assert_eq!(proof.pc_proof.is_hiding(), MM::ZK);
        proof.print_size_info();
        end_timer!(prover_time);

        Ok(proof)
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
            let domain_x = EvaluationDomain::<TargetField>::new(public_input.len() + 1).unwrap();

            if cfg!(debug_assertions) {
                println!("Number of given public inputs: {}", public_input.len());
                println!("Size of evaluation domain x: {}", domain_x.size());
            }

            let mut new_input = vec![TargetField::one()];
            new_input.extend_from_slice(&public_input);
            new_input.resize(core::cmp::max(public_input.len(), domain_x.size()), TargetField::zero());
            assert!(new_input.first().unwrap().is_one());
            new_input
        };
        let public_input = ProverConstraintSystem::unformat_public_input(&padded_public_input);

        if cfg!(debug_assertions) {
            println!("Number of padded public variables: {}", padded_public_input.len());
        }

        let mut fs_rng = FS::with_parameters(fs_parameters);

        if MM::RECURSION {
            fs_rng.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
            fs_rng.absorb_native_field_elements(&circuit_verifying_key.circuit_commitments);
            fs_rng.absorb_nonnative_field_elements(&padded_public_input, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(
                &to_bytes_le![&Self::PROTOCOL_NAME, &circuit_verifying_key, padded_public_input].unwrap(),
            );
        }

        // --------------------------------------------------------------------
        // First round

        if MM::RECURSION {
            fs_rng.absorb_native_field_elements(&first_commitments);
            if !proof.prover_messages[0].field_elements.is_empty() {
                fs_rng.absorb_nonnative_field_elements(
                    &proof.prover_messages[0].field_elements,
                    OptimizationType::Weight,
                );
            };
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![first_commitments, proof.prover_messages[0]].unwrap());
        }

        let (_, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_first_round(circuit_verifying_key.circuit_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        if MM::RECURSION {
            fs_rng.absorb_native_field_elements(&second_commitments);
            if !proof.prover_messages[1].field_elements.is_empty() {
                fs_rng.absorb_nonnative_field_elements(
                    &proof.prover_messages[1].field_elements,
                    OptimizationType::Weight,
                );
            };
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![second_commitments, proof.prover_messages[1]].unwrap());
        }

        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        if MM::RECURSION {
            fs_rng.absorb_native_field_elements(&third_commitments);
            if !proof.prover_messages[2].field_elements.is_empty() {
                fs_rng.absorb_nonnative_field_elements(
                    &proof.prover_messages[2].field_elements,
                    OptimizationType::Weight,
                );
            };
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![third_commitments, proof.prover_messages[2]].unwrap());
        }

        let verifier_state = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = circuit_verifying_key.circuit_info;
        let degree_bounds = vec![None; circuit_verifying_key.circuit_commitments.len()]
            .into_iter()
            .chain(AHPForR1CS::<_, MM>::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::<_, MM>::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::<_, MM>::prover_third_round_degree_bounds(&index_info));

        let polynomial_labels = AHPForR1CS::<TargetField, MM>::polynomial_labels();

        // Gather commitments in one vector.
        let commitments: Vec<_> = circuit_verifying_key
            .iter()
            .chain(first_commitments)
            .chain(second_commitments)
            .chain(third_commitments)
            .cloned()
            .zip(polynomial_labels)
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state, &mut fs_rng);

        if MM::RECURSION {
            fs_rng.absorb_nonnative_field_elements(&proof.evaluations, OptimizationType::Weight);
        } else {
            fs_rng.absorb_bytes(&to_bytes_le![&proof.evaluations].unwrap());
        }

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
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(q, *eval);
        }

        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(&public_input, &evaluations, &verifier_state)?;

        let evaluations_are_correct = if MM::RECURSION {
            let num_open_challenges: usize = 7;

            let mut opening_challenges = Vec::new();
            opening_challenges.append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges)?);

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
        } else {
            let opening_challenge: TargetField = fs_rng.squeeze_128_bits_nonnative_field_elements(1)?[0];

            PC::check_combinations(
                &circuit_verifying_key.verifier_key,
                &lc_s,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                opening_challenge,
                &mut fs_rng,
            )?
        };

        if !evaluations_are_correct {
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
