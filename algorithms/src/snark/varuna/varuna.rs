// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::Certificate;
use crate::{
    AlgebraicSponge,
    SNARK,
    SNARKError,
    fft::EvaluationDomain,
    polycommit::sonic_pc::{
        Commitment,
        CommitterUnionKey,
        Evaluations,
        LabeledCommitment,
        QuerySet,
        Randomness,
        SonicKZG10,
    },
    r1cs::{ConstraintSynthesizer, SynthesisError},
    snark::varuna::{
        CircuitProvingKey,
        CircuitVerifyingKey,
        Proof,
        SNARKMode,
        UniversalSRS,
        ahp::{AHPError, AHPForR1CS, CircuitId, EvaluationsProvider},
        proof,
        prover,
        witness_label,
    },
    srs::UniversalVerifier,
};
use rand::RngCore;
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{One, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{ToBytes, to_bytes_le};

use anyhow::{Result, anyhow, bail, ensure};
use core::marker::PhantomData;
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{borrow::Borrow, collections::BTreeMap, ops::Deref, sync::Arc};

use crate::srs::UniversalProver;
use snarkvm_utilities::println;

/// The Varuna proof system.
#[derive(Clone, Debug)]
pub struct VarunaSNARK<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, SM: SNARKMode>(
    #[doc(hidden)] PhantomData<(E, FS, SM)>,
);

impl<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, SM: SNARKMode> VarunaSNARK<E, FS, SM> {
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"VARUNA-2023";

    // TODO: implement optimizations resulting from batching
    //       (e.g. computing a common set of Lagrange powers, FFT precomputations, etc)
    pub fn batch_circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &UniversalSRS<E>,
        circuits: &[&C],
    ) -> Result<Vec<(CircuitProvingKey<E, SM>, CircuitVerifyingKey<E>)>> {
        let index_time = start_timer!(|| "Varuna::CircuitSetup");

        let universal_prover = &universal_srs.to_universal_prover()?;

        let mut circuit_keys = Vec::with_capacity(circuits.len());
        for circuit in circuits {
            let mut indexed_circuit = AHPForR1CS::<_, SM>::index(*circuit)?;
            // TODO: Add check that c is in the correct mode.
            // Ensure the universal SRS supports the circuit size.
            universal_srs.download_powers_for(0..indexed_circuit.max_degree()?).map_err(|e| {
                anyhow!("Failed to download powers for degree {}: {e}", indexed_circuit.max_degree().unwrap())
            })?;
            let coefficient_support = AHPForR1CS::<E::Fr, SM>::get_degree_bounds(&indexed_circuit.index_info)?;

            // Varuna only needs degree 2 random polynomials.
            let supported_hiding_bound = 1;
            let supported_lagrange_sizes = [].into_iter(); // TODO: consider removing lagrange_bases_at_beta_g from CommitterKey
            let (committer_key, _) = SonicKZG10::<E, FS>::trim(
                universal_srs,
                indexed_circuit.max_degree()?,
                supported_lagrange_sizes,
                supported_hiding_bound,
                Some(coefficient_support.as_slice()),
            )?;

            let ck = CommitterUnionKey::union(std::iter::once(&committer_key));

            let commit_time = start_timer!(|| format!("Commit to index polynomials for {}", indexed_circuit.id));
            let setup_rng = None::<&mut dyn RngCore>; // We do not randomize the commitments

            let (mut circuit_commitments, commitment_randomnesses): (_, _) = SonicKZG10::<E, FS>::commit(
                universal_prover,
                &ck,
                indexed_circuit.interpolate_matrix_evals()?.map(Into::into),
                setup_rng,
            )?;
            let empty_randomness = Randomness::<E>::empty();
            ensure!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
            end_timer!(commit_time);

            circuit_commitments.sort_by(|c1, c2| c1.label().cmp(c2.label()));
            let circuit_commitments = circuit_commitments.into_iter().map(|c| *c.commitment()).collect();
            indexed_circuit.prune_row_col_evals();
            let circuit_verifying_key = CircuitVerifyingKey {
                circuit_info: indexed_circuit.index_info,
                circuit_commitments,
                id: indexed_circuit.id,
            };
            let circuit_proving_key = CircuitProvingKey {
                circuit_verifying_key: circuit_verifying_key.clone(),
                circuit: Arc::new(indexed_circuit),
                committer_key: Arc::new(committer_key),
            };
            circuit_keys.push((circuit_proving_key, circuit_verifying_key));
        }

        end_timer!(index_time);
        Ok(circuit_keys)
    }

    fn init_sponge<'a>(
        fs_parameters: &FS::Parameters,
        inputs_and_batch_sizes: &BTreeMap<CircuitId, (usize, &[Vec<E::Fr>])>,
        circuit_commitments: impl Iterator<Item = &'a [crate::polycommit::sonic_pc::Commitment<E>]>,
    ) -> FS {
        let mut sponge = FS::new_with_parameters(fs_parameters);
        sponge.absorb_bytes(Self::PROTOCOL_NAME);
        for (batch_size, inputs) in inputs_and_batch_sizes.values() {
            sponge.absorb_bytes(&(*batch_size as u64).to_le_bytes());
            for input in inputs.iter() {
                sponge.absorb_nonnative_field_elements(input.iter().copied());
            }
        }
        for circuit_specific_commitments in circuit_commitments {
            sponge.absorb_native_field_elements(circuit_specific_commitments);
        }
        sponge
    }

    fn init_sponge_for_certificate(
        fs_parameters: &FS::Parameters,
        verifying_key: &CircuitVerifyingKey<E>,
    ) -> Result<FS> {
        let mut sponge = FS::new_with_parameters(fs_parameters);
        sponge.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME]?);
        sponge.absorb_bytes(&verifying_key.circuit_info.to_bytes_le()?);
        sponge.absorb_native_field_elements(&verifying_key.circuit_commitments);
        sponge.absorb_bytes(&verifying_key.id.0);
        Ok(sponge)
    }

    fn absorb_labeled_with_sums(
        comms: &[LabeledCommitment<Commitment<E>>],
        sums: &[prover::MatrixSums<E::Fr>],
        sponge: &mut FS,
    ) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::absorb_with_sums(&commitments, sums, sponge)
    }

    fn absorb_labeled(comms: &[LabeledCommitment<Commitment<E>>], sponge: &mut FS) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::absorb(&commitments, sponge);
    }

    fn absorb(commitments: &[Commitment<E>], sponge: &mut FS) {
        let sponge_time = start_timer!(|| "Absorbing commitments");
        sponge.absorb_native_field_elements(commitments);
        end_timer!(sponge_time);
    }

    fn absorb_with_sums(commitments: &[Commitment<E>], sums: &[prover::MatrixSums<E::Fr>], sponge: &mut FS) {
        let sponge_time = start_timer!(|| "Absorbing commitments and message");
        Self::absorb(commitments, sponge);
        for sum in sums.iter() {
            sponge.absorb_nonnative_field_elements([sum.sum_a, sum.sum_b, sum.sum_c]);
        }
        end_timer!(sponge_time);
    }
}

impl<E: PairingEngine, FS, SM> SNARK for VarunaSNARK<E, FS, SM>
where
    E::Fr: PrimeField,
    E::Fq: PrimeField,
    FS: AlgebraicSponge<E::Fq, 2>,
    SM: SNARKMode,
{
    type BaseField = E::Fq;
    type Certificate = Certificate<E>;
    type FSParameters = FS::Parameters;
    type FiatShamirRng = FS;
    type Proof = Proof<E>;
    type ProvingKey = CircuitProvingKey<E, SM>;
    type ScalarField = E::Fr;
    type UniversalProver = UniversalProver<E>;
    type UniversalSRS = UniversalSRS<E>;
    type UniversalVerifier = UniversalVerifier<E>;
    type VerifierInput = [E::Fr];
    type VerifyingKey = CircuitVerifyingKey<E>;

    fn universal_setup(max_degree: usize) -> Result<Self::UniversalSRS> {
        let setup_time = start_timer!(|| { format!("Varuna::UniversalSetup with max_degree {max_degree}",) });
        let srs = SonicKZG10::<E, FS>::load_srs(max_degree).map_err(Into::into);
        end_timer!(setup_time);
        srs
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    fn circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &Self::UniversalSRS,
        circuit: &C,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey)> {
        let mut circuit_keys = Self::batch_circuit_setup::<C>(universal_srs, &[circuit])?;
        ensure!(circuit_keys.len() == 1);
        Ok(circuit_keys.pop().unwrap())
    }

    /// Prove that the verifying key commitments commit to the indexed circuit's polynomials
    fn prove_vk(
        universal_prover: &Self::UniversalProver,
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        proving_key: &Self::ProvingKey,
    ) -> Result<Self::Certificate> {
        // Initialize sponge
        let mut sponge = Self::init_sponge_for_certificate(fs_parameters, verifying_key)?;
        // Compute challenges for linear combination, and the point to evaluate the polynomials at.
        // The linear combination requires `num_polynomials - 1` coefficients
        // (since the first coeff is 1), and so we squeeze out `num_polynomials` points.
        let mut challenges = sponge.squeeze_nonnative_field_elements(verifying_key.circuit_commitments.len());
        let point = challenges.pop().ok_or(anyhow!("Failed to squeeze random element"))?;
        let one = E::Fr::one();
        let linear_combination_challenges = core::iter::once(&one).chain(challenges.iter());

        let circuit_id = std::iter::once(&verifying_key.id);
        let circuit_poly_info = AHPForR1CS::<E::Fr, SM>::index_polynomial_info(circuit_id);

        // We will construct a linear combination and provide a proof of evaluation of the lc at `point`.
        let mut lc = crate::polycommit::sonic_pc::LinearCombination::empty("circuit_check");
        for (label, &c) in circuit_poly_info.keys().zip(linear_combination_challenges) {
            lc.add(c, label.clone());
        }

        let query_set = QuerySet::from_iter([("circuit_check".into(), ("challenge".into(), point))]);
        let committer_key = CommitterUnionKey::union(std::iter::once(proving_key.committer_key.as_ref()));

        let empty_randomness = vec![Randomness::<E>::empty(); 12];
        let certificate = SonicKZG10::<E, FS>::open_combinations(
            universal_prover,
            &committer_key,
            &[lc],
            proving_key.circuit.interpolate_matrix_evals()?,
            &empty_randomness,
            &query_set,
            &mut sponge,
        )?;

        Ok(Self::Certificate::new(certificate))
    }

    /// Verify that the verifying key commitments commit to the indexed circuit's polynomials
    /// Verify that the verifying key's circuit_info is correct
    fn verify_vk<C: ConstraintSynthesizer<Self::ScalarField>>(
        universal_verifier: &Self::UniversalVerifier,
        fs_parameters: &Self::FSParameters,
        circuit: &C,
        verifying_key: &Self::VerifyingKey,
        certificate: &Self::Certificate,
    ) -> Result<bool> {
        // Ensure the VerifyingKey encodes the expected circuit.
        let circuit_id = &verifying_key.id;
        let state = AHPForR1CS::<E::Fr, SM>::index_helper(circuit)?;
        if state.index_info != verifying_key.circuit_info {
            bail!(SNARKError::CircuitNotFound);
        }
        if state.id != *circuit_id {
            bail!(SNARKError::CircuitNotFound);
        }

        // Initialize sponge.
        let mut sponge = Self::init_sponge_for_certificate(fs_parameters, verifying_key)?;

        // Compute challenges for linear combination, and the point to evaluate the polynomials at.
        // The linear combination requires `num_polynomials - 1` coefficients
        // (since the first coeff is 1), and so we squeeze out `num_polynomials` points.
        let mut challenges = sponge.squeeze_nonnative_field_elements(verifying_key.circuit_commitments.len());
        let point = challenges.pop().ok_or(anyhow!("Failed to squeeze random element"))?;
        let combiners = core::iter::once(E::Fr::one()).chain(challenges);

        // We will construct a linear combination and provide a proof of evaluation of the lc at `point`.
        let (lc, evaluation) =
            AHPForR1CS::<E::Fr, SM>::evaluate_index_polynomials(state, circuit_id, point, combiners)?;

        ensure!(verifying_key.circuit_commitments.len() == lc.terms.len());
        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(lc.terms.keys())
            .map(|(c, label)| LabeledCommitment::new(format!("{label:?}"), c, None))
            .collect_vec();
        let evaluations = Evaluations::from_iter([(("circuit_check".into(), point), evaluation)]);
        let query_set = QuerySet::from_iter([("circuit_check".into(), ("challenge".into(), point))]);

        SonicKZG10::<E, FS>::check_combinations(
            universal_verifier,
            &[lc],
            &commitments,
            &query_set,
            &evaluations,
            &certificate.pc_proof,
            &mut sponge,
        )
        .map_err(Into::into)
    }

    /// This is the main entrypoint for creating proofs.
    /// You can find a specification of the prover algorithm in:
    /// https://github.com/AleoNet/protocol-docs
    fn prove_batch<C: ConstraintSynthesizer<E::Fr>, R: Rng + CryptoRng>(
        universal_prover: &Self::UniversalProver,
        fs_parameters: &Self::FSParameters,
        keys_to_constraints: &BTreeMap<&CircuitProvingKey<E, SM>, &[C]>,
        zk_rng: &mut R,
    ) -> Result<Self::Proof> {
        let prover_time = start_timer!(|| "Varuna::Prover");
        if keys_to_constraints.is_empty() {
            bail!(SNARKError::EmptyBatch);
        }

        let mut circuits_to_constraints = BTreeMap::new();
        for (pk, constraints) in keys_to_constraints {
            circuits_to_constraints.insert(pk.circuit.deref(), *constraints);
        }
        let prover_state = AHPForR1CS::<_, SM>::init_prover(&circuits_to_constraints, zk_rng)?;

        // extract information from the prover key and state to consume in further calculations
        let mut batch_sizes = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut total_instances = 0usize;
        let mut public_inputs = BTreeMap::new(); // inputs need to live longer than the rest of prover_state
        let num_unique_circuits = keys_to_constraints.len();
        let mut circuit_ids = Vec::with_capacity(num_unique_circuits);
        for pk in keys_to_constraints.keys() {
            let batch_size = prover_state.batch_size(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let public_input = prover_state.public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let padded_public_input =
                prover_state.padded_public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let circuit_id = pk.circuit.id;
            batch_sizes.insert(circuit_id, batch_size);
            circuit_infos.insert(circuit_id, &pk.circuit_verifying_key.circuit_info);
            inputs_and_batch_sizes.insert(circuit_id, (batch_size, padded_public_input));
            public_inputs.insert(circuit_id, public_input);
            total_instances = total_instances.saturating_add(batch_size);

            circuit_ids.push(circuit_id);
        }
        ensure!(prover_state.total_instances == total_instances);

        let committer_key = CommitterUnionKey::union(keys_to_constraints.keys().map(|pk| pk.committer_key.deref()));

        let circuit_commitments =
            keys_to_constraints.keys().map(|pk| pk.circuit_verifying_key.circuit_commitments.as_slice());

        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round

        let prover_state = AHPForR1CS::<_, SM>::prover_first_round(prover_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) = {
            let first_round_oracles = prover_state.first_round_oracles.as_ref().unwrap();
            SonicKZG10::<E, FS>::commit(
                universal_prover,
                &committer_key,
                first_round_oracles.iter().map(Into::into),
                SM::ZK.then_some(zk_rng),
            )?
        };
        end_timer!(first_round_comm_time);

        Self::absorb_labeled(&first_commitments, &mut sponge);

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, SM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            prover_state.max_constraint_domain,
            prover_state.max_variable_domain,
            prover_state.max_non_zero_domain,
            &mut sponge,
        )?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (second_oracles, prover_state) =
            AHPForR1CS::<_, SM>::prover_second_round(&verifier_first_message, prover_state, zk_rng)?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitments, second_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            second_oracles.iter().map(Into::into),
            SM::ZK.then_some(zk_rng),
        )?;
        end_timer!(second_round_comm_time);

        Self::absorb_labeled(&second_commitments, &mut sponge);

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, SM>::verifier_second_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        let (prover_third_message, third_oracles, prover_state) = AHPForR1CS::<_, SM>::prover_third_round(
            &verifier_first_message,
            &verifier_second_msg,
            prover_state,
            zk_rng,
        )?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitments, third_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            third_oracles.iter().map(Into::into),
            SM::ZK.then_some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        Self::absorb_labeled_with_sums(
            &third_commitments,
            &prover_third_message.sums.clone().into_iter().flatten().collect_vec(),
            &mut sponge,
        );

        let (verifier_third_msg, verifier_state) =
            AHPForR1CS::<_, SM>::verifier_third_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round

        let (prover_fourth_message, fourth_oracles, mut prover_state) =
            AHPForR1CS::<_, SM>::prover_fourth_round(&verifier_second_msg, &verifier_third_msg, prover_state, zk_rng)?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_commitments, fourth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            fourth_oracles.iter().map(Into::into),
            SM::ZK.then_some(zk_rng),
        )?;
        end_timer!(fourth_round_comm_time);

        Self::absorb_labeled_with_sums(&fourth_commitments, &prover_fourth_message.sums, &mut sponge);

        let (verifier_fourth_msg, verifier_state) =
            AHPForR1CS::<_, SM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // We take out values from state before they are consumed.
        let first_round_oracles = prover_state.first_round_oracles.take().unwrap();
        let index_a_polys =
            prover_state.circuit_specific_states.values_mut().flat_map(|s| s.a_polys.take().unwrap()).collect_vec();
        let index_b_polys =
            prover_state.circuit_specific_states.values_mut().flat_map(|s| s.b_polys.take().unwrap()).collect_vec();

        // --------------------------------------------------------------------
        // Fifth round
        let fifth_oracles = AHPForR1CS::<_, SM>::prover_fifth_round(verifier_fourth_msg, prover_state, zk_rng)?;

        let fifth_round_comm_time = start_timer!(|| "Committing to fifth round polys");
        let (fifth_commitments, fifth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            fifth_oracles.iter().map(Into::into),
            SM::ZK.then_some(zk_rng),
        )?;
        end_timer!(fifth_round_comm_time);

        Self::absorb_labeled(&fifth_commitments, &mut sponge);

        let verifier_state = AHPForR1CS::<_, SM>::verifier_fifth_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_a_polys
            .into_iter()
            .chain(index_b_polys)
            .chain(first_round_oracles.into_iter())
            .chain(second_oracles.into_iter())
            .chain(third_oracles.into_iter())
            .chain(fourth_oracles.into_iter())
            .chain(fifth_oracles.into_iter())
            .collect();
        ensure!(
            polynomials.len()
                == num_unique_circuits * 6 + // numerator and denominator for each matrix sumcheck
            AHPForR1CS::<E::Fr, SM>::num_first_round_oracles(total_instances) +
            AHPForR1CS::<E::Fr, SM>::num_second_round_oracles() +
            AHPForR1CS::<E::Fr, SM>::num_third_round_oracles() +
            AHPForR1CS::<E::Fr, SM>::num_fourth_round_oracles(num_unique_circuits) +
            AHPForR1CS::<E::Fr, SM>::num_fifth_round_oracles()
        );

        // Gather commitments in one vector.
        let witness_comm_len = if SM::ZK { first_commitments.len() - 1 } else { first_commitments.len() };
        let mask_poly = SM::ZK.then(|| *first_commitments[witness_comm_len].commitment());
        let witness_commitments = first_commitments[..witness_comm_len]
            .iter()
            .map(|c| proof::WitnessCommitments { w: *c.commitment() })
            .collect_vec();
        let fourth_commitments_chunked = fourth_commitments.chunks_exact(3);
        let (g_a_commitments, g_b_commitments, g_c_commitments) = fourth_commitments_chunked
            .map(|c| (*c[0].commitment(), *c[1].commitment(), *c[2].commitment()))
            .multiunzip();

        #[rustfmt::skip]
        let commitments = proof::Commitments {
            witness_commitments,
            mask_poly,
            h_0: *second_commitments[0].commitment(),
            g_1: *third_commitments[0].commitment(),
            h_1: *third_commitments[1].commitment(),
            g_a_commitments,
            g_b_commitments,
            g_c_commitments,
            h_2: *fifth_commitments[0].commitment(),
        };

        // Gather commitment randomness together.
        let indexer_randomness = vec![Randomness::<E>::empty(); 6 * num_unique_circuits];
        let commitment_randomnesses: Vec<Randomness<E>> = indexer_randomness
            .into_iter()
            .chain(first_commitment_randomnesses)
            .chain(second_commitment_randomnesses)
            .chain(third_commitment_randomnesses)
            .chain(fourth_commitment_randomnesses)
            .chain(fifth_commitment_randomnesses)
            .collect();

        let empty_randomness = Randomness::<E>::empty();
        if SM::ZK {
            ensure!(commitment_randomnesses.iter().any(|r| r != &empty_randomness));
        } else {
            ensure!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
        }

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::<_, SM>::verifier_query_set(verifier_state);
        let lc_s = AHPForR1CS::<_, SM>::construct_linear_combinations(
            &public_inputs,
            &polynomials,
            &prover_third_message,
            &prover_fourth_message,
            &verifier_state,
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = std::collections::BTreeMap::new();
        for (label, (_, point)) in query_set.to_set() {
            if !AHPForR1CS::<E::Fr, SM>::LC_WITH_ZERO_EVAL.contains(&label.as_str()) {
                let lc = lc_s.get(&label).ok_or_else(|| AHPError::MissingEval(label.to_string()))?;
                let evaluation = polynomials.get_lc_eval(lc, point)?;
                evaluations.insert(label, evaluation);
            }
        }

        let evaluations = proof::Evaluations::from_map(&evaluations, batch_sizes.clone());
        end_timer!(eval_time);

        sponge.absorb_nonnative_field_elements(evaluations.to_field_elements());

        let pc_proof = SonicKZG10::<E, FS>::open_combinations(
            universal_prover,
            &committer_key,
            lc_s.values(),
            polynomials,
            &commitment_randomnesses,
            &query_set.to_set(),
            &mut sponge,
        )?;

        let proof = Proof::<E>::new(
            batch_sizes,
            commitments,
            evaluations,
            prover_third_message,
            prover_fourth_message,
            pc_proof,
        )?;
        proof.check_batch_sizes()?;
        ensure!(proof.pc_proof.is_hiding() == SM::ZK);

        end_timer!(prover_time);
        Ok(proof)
    }

    /// This is the main entrypoint for verifying proofs.
    /// You can find a specification of the verifier algorithm in:
    /// https://github.com/AleoNet/protocol-docs
    fn verify_batch<B: Borrow<Self::VerifierInput>>(
        universal_verifier: &Self::UniversalVerifier,
        fs_parameters: &Self::FSParameters,
        keys_to_inputs: &BTreeMap<&Self::VerifyingKey, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool> {
        if keys_to_inputs.is_empty() {
            bail!(SNARKError::EmptyBatch);
        }

        proof.check_batch_sizes()?;
        let batch_sizes_vec = proof.batch_sizes();
        let mut batch_sizes = BTreeMap::new();
        for (i, (vk, public_inputs_i)) in keys_to_inputs.iter().enumerate() {
            batch_sizes.insert(vk.id, batch_sizes_vec[i]);

            if public_inputs_i.is_empty() {
                bail!(SNARKError::EmptyBatch);
            }

            if public_inputs_i.len() != batch_sizes_vec[i] {
                bail!(SNARKError::BatchSizeMismatch);
            }
        }

        // collect values into structures for our calculations
        let mut max_num_constraints = 0;
        let mut max_num_variables = 0;
        let mut max_non_zero_domain = None;
        let mut public_inputs = BTreeMap::new();
        let mut padded_public_vec = Vec::with_capacity(keys_to_inputs.len());
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut input_domains = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut circuit_ids = Vec::with_capacity(keys_to_inputs.len());
        for (&vk, &public_inputs_i) in keys_to_inputs.iter() {
            max_num_constraints = max_num_constraints.max(vk.circuit_info.num_constraints);
            max_num_variables = max_num_variables.max(vk.circuit_info.num_public_and_private_variables);

            let non_zero_domains = AHPForR1CS::<_, SM>::cmp_non_zero_domains(&vk.circuit_info, max_non_zero_domain)?;
            max_non_zero_domain = non_zero_domains.max_non_zero_domain;

            let input_domain = EvaluationDomain::<E::Fr>::new(vk.circuit_info.num_public_inputs)
                .ok_or(anyhow!("Failed to create EvaluationDomain from num_public_inputs"))?;
            input_domains.insert(vk.id, input_domain);

            let input_fields = public_inputs_i
                .iter()
                .map(|input| {
                    let input = input.borrow().to_field_elements()?;
                    ensure!(input.len() > 0);
                    ensure!(input[0] == E::Fr::one());
                    if input.len() > input_domain.size() {
                        bail!(SNARKError::PublicInputSizeMismatch);
                    }
                    Ok(input)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let (padded_public_inputs_i, parsed_public_inputs_i): (Vec<_>, Vec<_>) = {
                input_fields
                    .iter()
                    .map(|input| {
                        let input_len = input.len().max(input_domain.size());
                        let mut new_input = Vec::with_capacity(input_len);
                        new_input.extend_from_slice(input);
                        new_input.resize(input_len, E::Fr::zero());
                        if cfg!(debug_assertions) {
                            println!("Number of padded public variables: {}", new_input.len());
                        }
                        let unformatted = prover::ConstraintSystem::unformat_public_input(&new_input);
                        (new_input, unformatted)
                    })
                    .unzip()
            };
            let circuit_id = vk.id;
            public_inputs.insert(circuit_id, parsed_public_inputs_i);
            padded_public_vec.push(padded_public_inputs_i);
            circuit_infos.insert(circuit_id, &vk.circuit_info);
            circuit_ids.push(circuit_id);
        }
        for (i, (vk, &batch_size)) in keys_to_inputs.keys().zip(batch_sizes.values()).enumerate() {
            inputs_and_batch_sizes.insert(vk.id, (batch_size, padded_public_vec[i].as_slice()));
        }
        let max_constraint_domain =
            EvaluationDomain::<E::Fr>::new(max_num_constraints).ok_or(SynthesisError::PolyTooLarge)?;
        let max_variable_domain =
            EvaluationDomain::<E::Fr>::new(max_num_variables).ok_or(SynthesisError::PolyTooLarge)?;
        let max_non_zero_domain = max_non_zero_domain.ok_or(SynthesisError::PolyTooLarge)?;

        let comms = &proof.commitments;
        let proof_has_correct_zk_mode = if SM::ZK {
            proof.pc_proof.is_hiding() & comms.mask_poly.is_some()
        } else {
            !proof.pc_proof.is_hiding() & comms.mask_poly.is_none()
        };
        if !proof_has_correct_zk_mode {
            eprintln!(
                "Found `mask_poly` in the first round when not expected, or proof has incorrect hiding mode ({})",
                proof.pc_proof.is_hiding()
            );
            return Ok(false);
        }

        let verifier_time = start_timer!(|| format!("Varuna::Verify with batch sizes: {:?}", batch_sizes));

        let first_round_info = AHPForR1CS::<E::Fr, SM>::first_round_polynomial_info(batch_sizes.iter());

        let mut first_comms_consumed = 0;
        let mut first_commitments = batch_sizes
            .iter()
            .flat_map(|(circuit_id, &batch_size)| {
                let first_comms = comms.witness_commitments[first_comms_consumed..][..batch_size]
                    .iter()
                    .enumerate()
                    .map(|(j, w_comm)| {
                        LabeledCommitment::new_with_info(
                            &first_round_info[&witness_label(*circuit_id, "w", j)],
                            w_comm.w,
                        )
                    });
                first_comms_consumed += batch_size;
                first_comms
            })
            .collect_vec();

        if SM::ZK {
            first_commitments.push(LabeledCommitment::new_with_info(
                first_round_info.get("mask_poly").ok_or(anyhow!("Missing mask_poly"))?,
                comms.mask_poly.ok_or(anyhow!("Missing mask_poly"))?,
            ));
        }

        let second_round_info = AHPForR1CS::<E::Fr, SM>::second_round_polynomial_info();
        let second_commitments = [LabeledCommitment::new_with_info(&second_round_info["h_0"], comms.h_0)];

        let third_round_info = AHPForR1CS::<E::Fr, SM>::third_round_polynomial_info(max_variable_domain.size());
        let third_commitments = [
            LabeledCommitment::new_with_info(&third_round_info["g_1"], comms.g_1),
            LabeledCommitment::new_with_info(&third_round_info["h_1"], comms.h_1),
        ];

        let fourth_round_info =
            AHPForR1CS::<E::Fr, SM>::fourth_round_polynomial_info(circuit_infos.clone().into_iter());
        let fourth_commitments = comms
            .g_a_commitments
            .iter()
            .zip_eq(comms.g_b_commitments.iter())
            .zip_eq(comms.g_c_commitments.iter())
            .zip_eq(circuit_ids.iter())
            .flat_map(|(((g_a, g_b), g_c), circuit_id)| {
                [
                    LabeledCommitment::new_with_info(&fourth_round_info[&witness_label(*circuit_id, "g_a", 0)], *g_a),
                    LabeledCommitment::new_with_info(&fourth_round_info[&witness_label(*circuit_id, "g_b", 0)], *g_b),
                    LabeledCommitment::new_with_info(&fourth_round_info[&witness_label(*circuit_id, "g_c", 0)], *g_c),
                ]
            })
            .collect_vec();

        let fifth_round_info = AHPForR1CS::<E::Fr, SM>::fifth_round_polynomial_info();
        let fifth_commitments = [LabeledCommitment::new_with_info(&fifth_round_info["h_2"], comms.h_2)];

        let circuit_commitments = keys_to_inputs.keys().map(|vk| vk.circuit_commitments.as_slice());
        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round
        let first_round_time = start_timer!(|| "First round");
        Self::absorb_labeled(&first_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, SM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            max_constraint_domain,
            max_variable_domain,
            max_non_zero_domain,
            &mut sponge,
        )?;
        end_timer!(first_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_round_time = start_timer!(|| "Second round");
        Self::absorb_labeled(&second_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, SM>::verifier_second_round(verifier_state, &mut sponge)?;
        end_timer!(second_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_round_time = start_timer!(|| "Third round");
        Self::absorb_labeled_with_sums(
            &third_commitments,
            &proof.third_msg.sums.clone().into_iter().flatten().collect_vec(),
            &mut sponge,
        );
        let (_, verifier_state) = AHPForR1CS::<_, SM>::verifier_third_round(verifier_state, &mut sponge)?;
        end_timer!(third_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round
        let fourth_round_time = start_timer!(|| "Fourth round");

        Self::absorb_labeled_with_sums(&fourth_commitments, &proof.fourth_msg.sums, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, SM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        end_timer!(fourth_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fifth round
        let fifth_round_time = start_timer!(|| "Fifth round");

        Self::absorb_labeled(&fifth_commitments, &mut sponge);
        let verifier_state = AHPForR1CS::<_, SM>::verifier_fifth_round(verifier_state, &mut sponge)?;
        end_timer!(fifth_round_time);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.

        let commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(AHPForR1CS::<E::Fr, SM>::index_polynomial_info(circuit_ids.iter()).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments)
            .chain(second_commitments)
            .chain(third_commitments)
            .chain(fourth_commitments)
            .chain(fifth_commitments)
            .collect();

        let query_set_time = start_timer!(|| "Constructing query set");
        let (query_set, verifier_state) = AHPForR1CS::<_, SM>::verifier_query_set(verifier_state);
        end_timer!(query_set_time);

        sponge.absorb_nonnative_field_elements(proof.evaluations.to_field_elements());

        let mut evaluations = Evaluations::new();

        let mut current_circuit_id = "".to_string();
        let mut circuit_index: i64 = -1;

        for (label, (_point_name, q)) in query_set.to_set() {
            if AHPForR1CS::<E::Fr, SM>::LC_WITH_ZERO_EVAL.contains(&label.as_ref()) {
                evaluations.insert((label, q), E::Fr::zero());
            } else {
                if label != "g_1" {
                    let circuit_id = CircuitId::from_witness_label(&label).to_string();
                    if circuit_id != current_circuit_id {
                        circuit_index += 1;
                        current_circuit_id = circuit_id;
                    }
                }
                let eval = proof
                    .evaluations
                    .get(circuit_index as usize, &label)
                    .ok_or_else(|| AHPError::MissingEval(label.clone()))?;
                evaluations.insert((label, q), eval);
            }
        }

        let lc_time = start_timer!(|| "Constructing linear combinations");
        let lc_s = AHPForR1CS::<_, SM>::construct_linear_combinations(
            &public_inputs,
            &evaluations,
            &proof.third_msg,
            &proof.fourth_msg,
            &verifier_state,
        )?;
        end_timer!(lc_time);

        let pc_time = start_timer!(|| "Checking linear combinations with PC");
        let evaluations_are_correct = SonicKZG10::<E, FS>::check_combinations(
            universal_verifier,
            lc_s.values(),
            &commitments,
            &query_set.to_set(),
            &evaluations,
            &proof.pc_proof,
            &mut sponge,
        )?;
        end_timer!(pc_time);

        if !evaluations_are_correct {
            #[cfg(debug_assertions)]
            eprintln!("SonicKZG10::Check failed using final challenge: {:?}", verifier_state.gamma);
        }

        end_timer!(verifier_time, || format!(
            " SonicKZG10::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct & proof_has_correct_zk_mode
        ));
        Ok(evaluations_are_correct & proof_has_correct_zk_mode)
    }
}
