// Copyright (C) 2019-2023 Aleo Systems Inc.
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
        ahp::{AHPError, AHPForR1CS, CircuitId, EvaluationsProvider},
        proof,
        prover,
        witness_label,
        BatchSize,
        CircuitProvingKey,
        CircuitVerifyingKey,
        Proof,
        SNARKMode,
        UniversalSRS,
    },
    srs::UniversalVerifier,
    AlgebraicSponge,
    SNARKError,
    SNARK,
};
use rand::RngCore;
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{One, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use anyhow::{anyhow, Result};
use core::marker::PhantomData;
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{borrow::Borrow, collections::BTreeMap, ops::Deref, sync::Arc};

use crate::srs::UniversalProver;
#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

/// The Varuna proof system.
#[derive(Clone, Debug)]
pub struct VarunaSNARK<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, MM: SNARKMode>(
    #[doc(hidden)] PhantomData<(E, FS, MM)>,
);

impl<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, MM: SNARKMode> VarunaSNARK<E, FS, MM> {
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"VARUNA-2023";

    // TODO: implement optimizations resulting from batching
    //       (e.g. computing a common set of Lagrange powers, FFT precomputations, etc)
    pub fn batch_circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &UniversalSRS<E>,
        circuits: &[&C],
    ) -> Result<Vec<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E>)>> {
        let index_time = start_timer!(|| "Varuna::CircuitSetup");

        let universal_prover = &universal_srs.to_universal_prover()?;

        let mut circuit_keys = Vec::with_capacity(circuits.len());
        for circuit in circuits {
            let mut indexed_circuit = AHPForR1CS::<_, MM>::index(*circuit)?;
            // TODO: Add check that c is in the correct mode.
            // Ensure the universal SRS supports the circuit size.
            universal_srs
                .download_powers_for(0..indexed_circuit.max_degree())
                .map_err(|e| anyhow!("Failed to download powers for degree {}: {e}", indexed_circuit.max_degree()))?;
            let coefficient_support = AHPForR1CS::<E::Fr, MM>::get_degree_bounds(&indexed_circuit.index_info);

            // Varuna only needs degree 2 random polynomials.
            let supported_hiding_bound = AHPForR1CS::<E::Fr, MM>::zk_bound().unwrap_or(0);
            let supported_lagrange_sizes = [].into_iter(); // TODO: consider removing lagrange_bases_at_beta_g from CommitterKey
            let (committer_key, _) = SonicKZG10::<E, FS>::trim(
                universal_srs,
                indexed_circuit.max_degree(),
                supported_lagrange_sizes,
                supported_hiding_bound,
                Some(coefficient_support.as_slice()),
            )?;

            let ck = CommitterUnionKey::union(std::iter::once(&committer_key));

            let commit_time = start_timer!(|| format!("Commit to index polynomials for {}", indexed_circuit.id));
            let setup_rng = None::<&mut dyn RngCore>; // We do not randomize the commitments
            let (mut circuit_commitments, circuit_commitment_randomness): (_, _) =
                SonicKZG10::<E, FS>::commit(universal_prover, &ck, indexed_circuit.iter().map(Into::into), setup_rng)?;
            end_timer!(commit_time);

            circuit_commitments.sort_by(|c1, c2| c1.label().cmp(c2.label()));
            println!("indexing circuit_commitments: {:?}", circuit_commitments);
            println!("indexing circuit_commitment_randomness: {:?}", circuit_commitment_randomness);
            let circuit_commitments = circuit_commitments.into_iter().map(|c| *c.commitment()).collect();
            indexed_circuit.prune_row_col_evals();
            let circuit_verifying_key = CircuitVerifyingKey {
                circuit_info: indexed_circuit.index_info,
                circuit_commitments,
                id: indexed_circuit.id,
            };
            let circuit_proving_key = CircuitProvingKey {
                circuit_verifying_key: circuit_verifying_key.clone(),
                circuit_commitment_randomness,
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
        sponge.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        for (batch_size, inputs) in inputs_and_batch_sizes.values() {
            sponge.absorb_bytes(&(u64::try_from(*batch_size).unwrap()).to_le_bytes());
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
        circuit_commitments: &[crate::polycommit::sonic_pc::Commitment<E>],
    ) -> FS {
        let mut sponge = FS::new_with_parameters(fs_parameters);
        sponge.absorb_bytes(&to_bytes_le![&Self::PROTOCOL_NAME].unwrap());
        sponge.absorb_native_field_elements(circuit_commitments);
        sponge
    }

    fn absorb_labeled_with_sums(
        comms: &[LabeledCommitment<Commitment<E>>],
        sums: impl IntoIterator<Item = E::Fr>,
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

    fn absorb_with_sums(commitments: &[Commitment<E>], sums: impl IntoIterator<Item = E::Fr>, sponge: &mut FS) {
        let sponge_time = start_timer!(|| "Absorbing commitments and message");
        Self::absorb(commitments, sponge);
        sponge.absorb_nonnative_field_elements(sums);
        end_timer!(sponge_time);
    }
}

impl<E: PairingEngine, FS, MM> SNARK for VarunaSNARK<E, FS, MM>
where
    E::Fr: PrimeField,
    E::Fq: PrimeField,
    FS: AlgebraicSponge<E::Fq, 2>,
    MM: SNARKMode,
{
    type BaseField = E::Fq;
    type Certificate = Certificate<E>;
    type FSParameters = FS::Parameters;
    type FiatShamirRng = FS;
    type Proof = Proof<E>;
    type ProvingKey = CircuitProvingKey<E, MM>;
    type ScalarField = E::Fr;
    type UniversalProver = UniversalProver<E>;
    type UniversalSRS = UniversalSRS<E>;
    type UniversalVerifier = UniversalVerifier<E>;
    type VerifierInput = [E::Fr];
    type VerifyingKey = CircuitVerifyingKey<E>;

    fn universal_setup(max_degree: usize) -> Result<Self::UniversalSRS, SNARKError> {
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
        assert_eq!(circuit_keys.len(), 1);
        Ok(circuit_keys.pop().unwrap())
    }

    /// Prove that the verifying key indeed includes a part of the reference string,
    /// as well as the indexed circuit (i.e. the circuit as a set of linear-sized polynomials).
    fn prove_vk(
        universal_prover: &Self::UniversalProver,
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        proving_key: &Self::ProvingKey,
    ) -> Result<Self::Certificate, SNARKError> {
        // Initialize sponge
        let mut sponge = Self::init_sponge_for_certificate(fs_parameters, &verifying_key.circuit_commitments);
        // Compute challenges for linear combination, and the point to evaluate the polynomials at.
        // The linear combination requires `num_polynomials - 1` coefficients
        // (since the first coeff is 1), and so we squeeze out `num_polynomials` points.
        let mut challenges = sponge.squeeze_nonnative_field_elements(verifying_key.circuit_commitments.len());
        let point = challenges.pop().unwrap();
        let one = E::Fr::one();
        let linear_combination_challenges = core::iter::once(&one).chain(challenges.iter());

        // We will construct a linear combination and provide a proof of evaluation of the lc at `point`.
        let mut lc = crate::polycommit::sonic_pc::LinearCombination::empty("circuit_check");
        for (poly, &c) in proving_key.circuit.iter().zip_eq(linear_combination_challenges) {
            lc.add(c, poly.label());
        }

        let lookups_used = proving_key.circuit.table_info.is_some();
        let circuit = std::iter::once((&verifying_key.id, lookups_used));
        let query_set = QuerySet::from_iter([("circuit_check".into(), (0, ("challenge".into(), point)))]);

        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, c))
            .collect::<Vec<_>>();

        let committer_key = CommitterUnionKey::union(std::iter::once(proving_key.committer_key.as_ref()));

        let certificate = SonicKZG10::<E, FS>::open_combinations(
            universal_prover,
            &committer_key,
            &[lc],
            proving_key.circuit.iter(),
            &commitments,
            &query_set,
            &proving_key.circuit_commitment_randomness.clone(),
            &mut sponge,
        )?;

        Ok(Self::Certificate::new(certificate))
    }

    /// Verify that the verifying key indeed includes a part of the reference string,
    /// as well as the indexed circuit (i.e. the circuit as a set of linear-sized polynomials).
    fn verify_vk<C: ConstraintSynthesizer<Self::ScalarField>>(
        universal_verifier: &Self::UniversalVerifier,
        fs_parameters: &Self::FSParameters,
        circuit: &C,
        verifying_key: &Self::VerifyingKey,
        certificate: &Self::Certificate,
    ) -> Result<bool, SNARKError> {
        let circuit_id = &verifying_key.id;
        // Initialize sponge.
        let mut sponge = Self::init_sponge_for_certificate(fs_parameters, &verifying_key.circuit_commitments);
        // Compute challenges for linear combination, and the point to evaluate the polynomials at.
        // The linear combination requires `num_polynomials - 1` coefficients
        // (since the first coeff is 1), and so we squeeze out `num_polynomials` points.
        let mut challenges = sponge.squeeze_nonnative_field_elements(verifying_key.circuit_commitments.len());
        let point = challenges.pop().unwrap();

        let evaluations_at_point = AHPForR1CS::<E::Fr, MM>::evaluate_index_polynomials(circuit, circuit_id, point)?;
        let one = E::Fr::one();
        let linear_combination_challenges = core::iter::once(&one).chain(challenges.iter());

        // We will construct a linear combination and provide a proof of evaluation of the lc at `point`.
        let mut lc = crate::polycommit::sonic_pc::LinearCombination::empty("circuit_check");
        let mut evaluation = E::Fr::zero();
        let lookups_used = verifying_key.circuit_commitments.len() > 12;
        let circuit_iter = std::iter::once((circuit_id, lookups_used));
        let info = AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_iter);
        for ((label, &c), eval) in info.keys().zip_eq(linear_combination_challenges).zip_eq(evaluations_at_point) {
            lc.add(c, label.as_str());
            evaluation += c * eval;
        }

        let query_set = QuerySet::from_iter([("circuit_check".into(), (0, ("challenge".into(), point)))]);
        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(info.values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, c))
            .collect::<Vec<_>>();
        let evaluations = Evaluations::from_iter([(("circuit_check".into(), point), evaluation)]);

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

    #[allow(clippy::only_used_in_recursion)]
    /// This is the main entrypoint for creating proofs.
    /// You can find a specification of the prover algorithm in:
    /// https://github.com/AleoHQ/protocol-docs/tree/main/marlin
    fn prove_batch<C: ConstraintSynthesizer<E::Fr>, R: Rng + CryptoRng>(
        universal_prover: &Self::UniversalProver,
        fs_parameters: &Self::FSParameters,
        keys_to_constraints: &BTreeMap<&CircuitProvingKey<E, MM>, &[C]>,
        zk_rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let prover_time = start_timer!(|| "Varuna::Prover");
        if keys_to_constraints.is_empty() {
            return Err(SNARKError::EmptyBatch);
        }

        let mut circuits_to_constraints = BTreeMap::new();
        for (pk, constraints) in keys_to_constraints {
            circuits_to_constraints.insert(pk.circuit.deref(), *constraints);
        }
        let prover_state = AHPForR1CS::<_, MM>::init_prover(&circuits_to_constraints, zk_rng)?;

        // extract information from the prover key and state to consume in further calculations
        let mut batch_sizes = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut total_instances = 0;
        let mut public_inputs = BTreeMap::new(); // inputs need to live longer than the rest of prover_state
        let num_unique_circuits = keys_to_constraints.len();
        let total_lookup_instances = prover_state.total_lookup_instances;
        let mut total_lookup_circuits = 0;
        let lookups_used = total_lookup_instances > 0;
        for pk in keys_to_constraints.keys() {
            let batch_size = prover_state.batch_size(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let public_input = prover_state.public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let padded_public_input =
                prover_state.padded_public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let circuit_id = pk.circuit.id;
            let lookups_used_i = pk.circuit.table_info.is_some();
            batch_sizes.insert(circuit_id, BatchSize { num_instances: batch_size, lookups_used: lookups_used_i });
            circuit_infos.insert(circuit_id, &pk.circuit_verifying_key.circuit_info);
            inputs_and_batch_sizes.insert(circuit_id, (batch_size, padded_public_input));
            total_instances += batch_size;
            if lookups_used_i {
                total_lookup_circuits += 1;
            }
            public_inputs.insert(circuit_id, public_input);
        }
        assert_eq!(prover_state.total_instances, total_instances);

        let committer_key = CommitterUnionKey::union(keys_to_constraints.keys().map(|pk| pk.committer_key.deref()));

        let circuit_commitments =
            keys_to_constraints.keys().map(|pk| pk.circuit_verifying_key.circuit_commitments.as_slice());

        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round

        let mut prover_state = AHPForR1CS::<_, MM>::prover_first_round(prover_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) = {
            let first_oracles = Arc::get_mut(prover_state.first_round_oracles.as_mut().unwrap()).unwrap();
            SonicKZG10::<E, FS>::commit(
                universal_prover,
                &committer_key,
                first_oracles.iter().map(Into::into),
                MM::ZK.then_some(zk_rng),
            )?
        };
        end_timer!(first_round_comm_time);

        Self::absorb_labeled(&first_commitments, &mut sponge);

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            prover_state.max_constraint_domain,
            prover_state.max_variable_domain,
            prover_state.max_non_zero_domain,
            &mut sponge,
        )?;
        let first_oracles = Arc::clone(prover_state.first_round_oracles.as_ref().unwrap());

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Lookup round
        let (lookup_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_lookup_round(&verifier_first_message, prover_state, zk_rng)?;

        let lookup_round_comm_time = start_timer!(|| "Committing to lookup round polys");
        let (lookup_commitments, lookup_commitment_randomnesses) = {
            SonicKZG10::<E, FS>::commit(
                universal_prover,
                &committer_key,
                lookup_oracles.iter().map(Into::into),
                Some(zk_rng),
            )?
        };
        end_timer!(lookup_round_comm_time);

        Self::absorb_labeled(&lookup_commitments, &mut sponge);

        let (verifier_lookup_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_lookup_round(verifier_state, lookups_used, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let mut prover_state = AHPForR1CS::<_, MM>::prover_second_round(
            &verifier_first_message,
            &verifier_lookup_msg,
            prover_state,
            zk_rng,
        )?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_commitments, second_commitment_randomnesses) = {
            let second_oracles = Arc::get_mut(prover_state.second_round_oracles.as_mut().unwrap()).unwrap();
            SonicKZG10::<E, FS>::commit(
                universal_prover,
                &committer_key,
                second_oracles.iter().map(Into::into),
                MM::ZK.then_some(zk_rng),
            )?
        };
        end_timer!(second_round_comm_time);

        Self::absorb_labeled(&second_commitments, &mut sponge);

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut sponge)?;
        let second_oracles = Arc::clone(prover_state.second_round_oracles.as_ref().unwrap());
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        let (prover_third_message, third_oracles, prover_state) = AHPForR1CS::<_, MM>::prover_third_round(
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
            MM::ZK.then_some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        Self::absorb_labeled_with_sums(&third_commitments, prover_third_message.clone().into_iter(), &mut sponge);

        let (verifier_third_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round

        let (prover_fourth_message, fourth_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_fourth_round(&verifier_second_msg, &verifier_third_msg, prover_state, zk_rng)?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_commitments, fourth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            fourth_oracles.iter().map(Into::into),
            MM::ZK.then_some(zk_rng),
        )?;
        end_timer!(fourth_round_comm_time);

        Self::absorb_labeled_with_sums(&fourth_commitments, prover_fourth_message.clone().into_iter(), &mut sponge);

        let (verifier_fourth_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fifth round

        let fifth_oracles = AHPForR1CS::<_, MM>::prover_fifth_round(verifier_fourth_msg, prover_state, zk_rng)?;

        let fifth_round_comm_time = start_timer!(|| "Committing to fifth round polys");
        let (fifth_commitments, fifth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit(
            universal_prover,
            &committer_key,
            fifth_oracles.iter().map(Into::into),
            MM::ZK.then_some(zk_rng),
        )?;
        end_timer!(fifth_round_comm_time);

        Self::absorb_labeled(&fifth_commitments, &mut sponge);

        let verifier_state = AHPForR1CS::<_, MM>::verifier_fifth_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = keys_to_constraints
            .keys()
            .flat_map(|pk| pk.circuit.iter())
            .chain(first_oracles.iter())
            .chain(lookup_oracles.iter())
            .chain(second_oracles.iter())
            .chain(third_oracles.iter())
            .chain(fourth_oracles.iter())
            .chain(fifth_oracles.iter())
            .collect();

        assert!(
            polynomials.len()
                == AHPForR1CS::<E::Fr, MM>::num_indexing_oracles(num_unique_circuits, total_lookup_circuits)
                    + AHPForR1CS::<E::Fr, MM>::num_first_round_oracles(total_instances, total_lookup_instances)
                    + AHPForR1CS::<E::Fr, MM>::num_lookup_round_oracles(total_lookup_instances)
                    + AHPForR1CS::<E::Fr, MM>::num_second_round_oracles(lookups_used)
                    + AHPForR1CS::<E::Fr, MM>::num_third_round_oracles()
                    + AHPForR1CS::<E::Fr, MM>::num_fourth_round_oracles(num_unique_circuits)
                    + AHPForR1CS::<E::Fr, MM>::num_fifth_round_oracles()
        );

        // Gather commitments in one vector.
        let mask_poly_0 = (MM::ZK && lookups_used).then(|| *second_commitments[2].commitment());
        let mask_poly_1 = MM::ZK.then(|| *second_commitments[1].commitment());
        let mut witness_commitments = Vec::with_capacity(total_instances);
        let mut instance_index = 0;
        for batch_size in batch_sizes.values() {
            for _ in 0..batch_size.num_instances {
                witness_commitments.push(proof::WitnessCommitments {
                    w: *first_commitments[instance_index].commitment(),
                    multiplicities: batch_size
                        .lookups_used
                        .then(|| *first_commitments[instance_index + 1].commitment()),
                });
                instance_index += batch_size.lookups_used.then_some(2).unwrap_or(1);
            }
        }

        let fourth_commitments_chunked = fourth_commitments.chunks_exact(3);

        let (g_a_commitments, g_b_commitments, g_c_commitments) = fourth_commitments_chunked
            .map(|c| (*c[0].commitment(), *c[1].commitment(), *c[2].commitment()))
            .multiunzip();
        let g_0_commitments = lookups_used.then(|| lookup_commitments.iter().map(|c| *c.commitment()).collect());
        let commitments = proof::Commitments {
            witness_commitments,
            mask_poly_0,
            g_0_commitments,
            h_0: *second_commitments[0].commitment(),
            mask_poly_1,
            g_1: *third_commitments[0].commitment(),
            h_1: *third_commitments[1].commitment(),
            g_a_commitments,
            g_b_commitments,
            g_c_commitments,
            h_2: *fifth_commitments[0].commitment(),
        };

        let labeled_commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(
                AHPForR1CS::<E::Fr, MM>::index_polynomial_info(batch_sizes.iter().map(|(id, b)| (id, b.lookups_used)))
                    .values(),
            )
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments.into_iter())
            .chain(lookup_commitments.into_iter())
            .chain(second_commitments.into_iter())
            .chain(third_commitments.into_iter())
            .chain(fourth_commitments.into_iter())
            .chain(fifth_commitments.into_iter())
            .collect();

        // Gather commitment randomness together.
        let commitment_randomnesses: Vec<Randomness<E>> = keys_to_constraints
            .keys()
            .flat_map(|pk| pk.circuit_commitment_randomness.clone())
            .chain(first_commitment_randomnesses)
            .chain(lookup_commitment_randomnesses)
            .chain(second_commitment_randomnesses)
            .chain(third_commitment_randomnesses)
            .chain(fourth_commitment_randomnesses)
            .chain(fifth_commitment_randomnesses)
            .collect();

        if !MM::ZK {
            let empty_randomness = Randomness::<E>::empty();
            assert!(commitment_randomnesses.iter().all(|r| r == &empty_randomness));
        }

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_inputs,
            &polynomials,
            &prover_third_message,
            &prover_fourth_message,
            &verifier_state,
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = std::collections::BTreeMap::new();
        for (label, (_, (_, point))) in query_set.to_set() {
            if !AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_str()) {
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
            &labeled_commitments,
            &query_set.to_set(),
            &commitment_randomnesses,
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
        assert_eq!(proof.pc_proof.is_hiding(), MM::ZK);

        end_timer!(prover_time);
        Ok(proof)
    }

    /// This is the main entrypoint for verifying proofs.
    /// You can find a specification of the verifier algorithm in:
    /// https://github.com/AleoHQ/protocol-docs/tree/main/marlin
    fn verify_batch<B: Borrow<Self::VerifierInput>>(
        universal_verifier: &Self::UniversalVerifier,
        fs_parameters: &Self::FSParameters,
        keys_to_inputs: &BTreeMap<&Self::VerifyingKey, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        if keys_to_inputs.is_empty() {
            return Err(SNARKError::EmptyBatch);
        }

        let batch_sizes_vec = proof.batch_sizes()?;
        let mut batch_sizes = BTreeMap::new();
        let mut num_instances = BTreeMap::new(); // TODO: we could get rid of this duplication if we also use BatchSize in poly_info(...), State, etc.
        for (i, (vk, public_inputs_i)) in keys_to_inputs.iter().enumerate() {
            batch_sizes.insert(vk.id, batch_sizes_vec[i].clone());
            num_instances.insert(vk.id, batch_sizes_vec[i].num_instances);

            if public_inputs_i.is_empty() {
                return Err(SNARKError::EmptyBatch);
            }

            if public_inputs_i.len() != batch_sizes_vec[i].num_instances {
                return Err(SNARKError::BatchSizeMismatch);
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
        for (vk, public_inputs_i) in keys_to_inputs.iter() {
            max_num_constraints = max_num_constraints.max(vk.circuit_info.num_constraints);
            max_num_variables = max_num_variables.max(vk.circuit_info.num_variables);

            let non_zero_domains = AHPForR1CS::<_, MM>::cmp_non_zero_domains(&vk.circuit_info, max_non_zero_domain)?;
            max_non_zero_domain = non_zero_domains.max_non_zero_domain;

            let input_domain = EvaluationDomain::<E::Fr>::new(vk.circuit_info.num_public_inputs).unwrap();
            input_domains.insert(vk.id, input_domain);

            let (padded_public_inputs_i, parsed_public_inputs_i): (Vec<_>, Vec<_>) = {
                public_inputs_i
                    .iter()
                    .map(|input| {
                        let input = input.borrow().to_field_elements().unwrap();
                        let mut new_input = vec![E::Fr::one()];
                        new_input.extend_from_slice(&input);
                        new_input.resize(input.len().max(input_domain.size()), E::Fr::zero());
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
        }
        for (i, (vk, &batch_size)) in keys_to_inputs.keys().zip(num_instances.values()).enumerate() {
            inputs_and_batch_sizes.insert(vk.id, (batch_size, padded_public_vec[i].as_slice()));
        }
        let max_constraint_domain =
            EvaluationDomain::<E::Fr>::new(max_num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let max_variable_domain =
            EvaluationDomain::<E::Fr>::new(max_num_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let max_non_zero_domain = max_non_zero_domain.ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let lookups_used = proof.commitments.g_0_commitments.is_some();
        let comms = &proof.commitments;
        // TODO: use mask_poly_0 for correctness check, create own function
        let proof_has_correct_zk_mode = if MM::ZK {
            proof.pc_proof.is_hiding() & comms.mask_poly_1.is_some()
        } else {
            !proof.pc_proof.is_hiding() & comms.mask_poly_1.is_none()
        };
        if !proof_has_correct_zk_mode {
            eprintln!(
                "Found `mask_poly` in the first round when not expected, or proof has incorrect hiding mode ({})",
                proof.pc_proof.is_hiding()
            );
            return Ok(false);
        }

        let verifier_time = start_timer!(|| format!("Varuna::Verify with batch sizes: {:?}", batch_sizes));

        let mut first_comms_consumed = 0;
        let first_round_info = AHPForR1CS::<E::Fr, MM>::first_round_polynomial_info(
            batch_sizes.iter().map(|(c, b)| (*c, b.num_instances, b.lookups_used)),
        );
        let mut first_commitments = Vec::with_capacity(comms.witness_commitments.len());
        for (circuit_id, batch_size) in &batch_sizes {
            for j in 0..batch_size.num_instances {
                first_commitments.push(LabeledCommitment::new_with_info(
                    &first_round_info[&witness_label(*circuit_id, "w", j)],
                    comms.witness_commitments[first_comms_consumed].w,
                ));
                if batch_size.lookups_used {
                    first_commitments.push(LabeledCommitment::new_with_info(
                        &first_round_info[&witness_label(*circuit_id, "multiplicities", j)],
                        comms.witness_commitments[first_comms_consumed].multiplicities.unwrap(),
                    ));
                }
                first_comms_consumed += 1;
            }
        }

        let mut lookup_commitments = vec![];
        if lookups_used {
            let mut lookup_comms_consumed = 0;
            let lookup_round_info = AHPForR1CS::<E::Fr, MM>::lookup_round_polynomial_info(
                circuit_infos.clone().into_iter().zip(num_instances.values()),
            );
            lookup_commitments = Vec::with_capacity(comms.g_0_commitments.as_ref().unwrap().len());
            for (circuit_id, batch_size) in &batch_sizes {
                if batch_size.lookups_used {
                    for j in 0..batch_size.num_instances {
                        lookup_commitments.push(LabeledCommitment::new_with_info(
                            &lookup_round_info[&witness_label(*circuit_id, "g_0", j)],
                            comms.g_0_commitments.as_ref().unwrap()[lookup_comms_consumed],
                        ));
                        lookup_comms_consumed += 1;
                    }
                }
            }
        }

        let second_round_info = AHPForR1CS::<E::Fr, MM>::second_round_polynomial_info(lookups_used);
        let mut second_commitments = vec![LabeledCommitment::new_with_info(&second_round_info["h_0"], comms.h_0)];

        if MM::ZK {
            second_commitments.push(LabeledCommitment::new_with_info(
                second_round_info.get("mask_poly_1").unwrap(),
                comms.mask_poly_1.unwrap(),
            ));
        }
        if MM::ZK && lookups_used {
            second_commitments.push(LabeledCommitment::new_with_info(
                second_round_info.get("mask_poly_0").unwrap(),
                comms.mask_poly_0.unwrap(),
            ));
        }

        let third_round_info = AHPForR1CS::<E::Fr, MM>::third_round_polynomial_info(max_variable_domain.size());
        let third_commitments = [
            LabeledCommitment::new_with_info(&third_round_info["g_1"], comms.g_1),
            LabeledCommitment::new_with_info(&third_round_info["h_1"], comms.h_1),
        ];

        let fourth_round_info =
            AHPForR1CS::<E::Fr, MM>::fourth_round_polynomial_info(circuit_infos.clone().into_iter());
        let fourth_commitments = comms
            .g_a_commitments
            .iter()
            .zip_eq(comms.g_b_commitments.iter())
            .zip_eq(comms.g_c_commitments.iter())
            .zip_eq(batch_sizes.keys())
            .flat_map(|(((g_a, g_b), g_c), circuit_id)| {
                [
                    LabeledCommitment::new_with_info(&fourth_round_info[&witness_label(*circuit_id, "g_a", 0)], *g_a),
                    LabeledCommitment::new_with_info(&fourth_round_info[&witness_label(*circuit_id, "g_b", 0)], *g_b),
                    LabeledCommitment::new_with_info(&fourth_round_info[&witness_label(*circuit_id, "g_c", 0)], *g_c),
                ]
            })
            .collect_vec();

        let fifth_round_info = AHPForR1CS::<E::Fr, MM>::fifth_round_polynomial_info();
        let fifth_commitments = [LabeledCommitment::new_with_info(&fifth_round_info["h_2"], comms.h_2)];

        let circuit_commitments = keys_to_inputs.keys().map(|vk| vk.circuit_commitments.as_slice());
        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round
        let first_round_time = start_timer!(|| "First round");
        Self::absorb_labeled(&first_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
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
        // Lookup round
        let lookup_round_time = start_timer!(|| "Lookup round");
        Self::absorb_labeled(&lookup_commitments, &mut sponge);
        let (_, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_lookup_round(verifier_state, lookups_used, &mut sponge)?;
        end_timer!(lookup_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_round_time = start_timer!(|| "Second round");
        Self::absorb_labeled(&second_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut sponge)?;
        end_timer!(second_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_round_time = start_timer!(|| "Third round");
        Self::absorb_labeled_with_sums(&third_commitments, proof.third_msg.clone().into_iter(), &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut sponge)?;
        end_timer!(third_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round
        let fourth_round_time = start_timer!(|| "Fourth round");

        Self::absorb_labeled_with_sums(&fourth_commitments, proof.fourth_msg.clone().into_iter(), &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        end_timer!(fourth_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fifth round
        let fifth_round_time = start_timer!(|| "Fifth round");

        Self::absorb_labeled(&fifth_commitments, &mut sponge);
        let verifier_state = AHPForR1CS::<_, MM>::verifier_fifth_round(verifier_state, &mut sponge)?;
        end_timer!(fifth_round_time);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.

        // Gather commitments in one vector.
        let commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(
                AHPForR1CS::<E::Fr, MM>::index_polynomial_info(batch_sizes.iter().map(|(id, b)| (id, b.lookups_used)))
                    .values(),
            )
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments)
            .chain(lookup_commitments)
            .chain(second_commitments)
            .chain(third_commitments)
            .chain(fourth_commitments)
            .chain(fifth_commitments)
            .collect();

        let query_set_time = start_timer!(|| "Constructing query set");
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);
        end_timer!(query_set_time);

        sponge.absorb_nonnative_field_elements(proof.evaluations.to_field_elements());

        let mut evaluations = Evaluations::new();
        for (label, (index, (_point_name, q))) in query_set.to_set() {
            if AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_ref()) {
                evaluations.insert((label, q), E::Fr::zero());
            } else {
                let eval = proof.evaluations.get(index, &label).ok_or_else(|| AHPError::MissingEval(label.clone()))?;
                evaluations.insert((label, q), eval);
            }
        }

        let lc_time = start_timer!(|| "Constructing linear combinations");
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
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
            eprintln!("SonicKZG10::Check failed using final challenge: {:?}", verifier_state.fifth_round_message);
        }

        end_timer!(verifier_time, || format!(
            " SonicKZG10::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct & proof_has_correct_zk_mode
        ));
        Ok(evaluations_are_correct & proof_has_correct_zk_mode)
    }
}
