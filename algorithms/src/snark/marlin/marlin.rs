// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    polycommit::sonic_pc::{
        Commitment,
        CommitterUnionKey,
        Evaluations,
        LabeledCommitment,
        QuerySet,
        Randomness,
        SonicKZG10,
        VerifierUnionKey,
    },
    snark::marlin::{
        ahp::{AHPError, AHPForR1CS, CircuitId, EvaluationsProvider},
        proof,
        prover,
        witness_label,
        CircuitProvingKey,
        CircuitVerifyingKey,
        MarlinError,
        MarlinMode,
        Proof,
        UniversalSRS,
    },
    AlgebraicSponge,
    PrepareOrd,
    SNARKError,
    SNARK,
    SRS,
};
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{One, PrimeField, ToConstraintField, Zero};
use snarkvm_r1cs::ConstraintSynthesizer;
use snarkvm_utilities::{to_bytes_le, ToBytes};

use std::{borrow::Borrow, collections::BTreeMap, ops::Deref, sync::Arc};

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicBool, Ordering},
};

use super::Certificate;

/// The Marlin proof system.
#[derive(Clone, Debug)]
pub struct MarlinSNARK<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, MM: MarlinMode>(
    #[doc(hidden)] PhantomData<(E, FS, MM)>,
);

impl<E: PairingEngine, FS: AlgebraicSponge<E::Fq, 2>, MM: MarlinMode> MarlinSNARK<E, FS, MM> {
    /// The personalization string for this protocol.
    /// Used to personalize the Fiat-Shamir RNG.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a trusted setup.
    ///
    /// # Warning
    ///
    /// This method should be used *only* for testing purposes, and not in production.
    /// In production, one should instead perform a universal setup via [`Self::universal_setup`],
    /// and then deterministically specialize the resulting universal SRS via [`Self::circuit_setup`].
    #[allow(clippy::type_complexity)]
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<E::Fr>>(
        circuit: &C,
    ) -> Result<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E, MM>), SNARKError> {
        let indexed_circuit = AHPForR1CS::<E::Fr, MM>::index(circuit)?;
        let srs = Self::universal_setup(&indexed_circuit.max_degree())?;
        Self::circuit_setup(&srs, circuit)
    }

    // TODO: implement optimizations resulting from batching
    //       (e.g. computing a common set of Lagrange powers, FFT precomputations, etc)
    pub fn batch_circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &UniversalSRS<E>,
        circuits: &[&C],
    ) -> Result<Vec<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E, MM>)>, SNARKError> {
        let index_time = start_timer!(|| "Marlin::CircuitSetup");

        let mut circuit_keys = Vec::with_capacity(circuits.len());
        for circuit in circuits {
            let indexed_circuit = AHPForR1CS::<_, MM>::index(*circuit)?;
            // TODO: Add check that c is in the correct mode.
            // Increase the universal SRS size to support the circuit size.
            if universal_srs.max_degree() < indexed_circuit.max_degree() {
                universal_srs.download_powers_for(0..indexed_circuit.max_degree()).map_err(|_| {
                    MarlinError::IndexTooLarge(universal_srs.max_degree(), indexed_circuit.max_degree())
                })?;
            }
            let coefficient_support = AHPForR1CS::<_, MM>::get_degree_bounds(&indexed_circuit.index_info);

            // Marlin only needs degree 2 random polynomials.
            let supported_hiding_bound = 1;
            let (committer_key, verifier_key) = SonicKZG10::<E, FS>::trim(
                universal_srs,
                indexed_circuit.max_degree(),
                [indexed_circuit.constraint_domain_size()],
                supported_hiding_bound,
                Some(coefficient_support.as_slice()),
            )?;

            let ck = CommitterUnionKey::union(std::iter::once(&committer_key));

            let commit_time = start_timer!(|| format!("Commit to index polynomials for {}", indexed_circuit.id));
            let (mut circuit_commitments, circuit_commitment_randomness): (_, _) =
                SonicKZG10::<E, FS>::commit(&ck, indexed_circuit.iter().map(Into::into), None)?;
            end_timer!(commit_time);

            circuit_commitments.sort_by(|c1, c2| c1.label().cmp(c2.label()));
            let circuit_commitments = circuit_commitments.into_iter().map(|c| *c.commitment()).collect();
            let circuit_verifying_key = CircuitVerifyingKey {
                circuit_info: indexed_circuit.index_info,
                circuit_commitments,
                verifier_key,
                mode: PhantomData,
                id: indexed_circuit.id,
            };
            let circuit_proving_key = CircuitProvingKey {
                circuit: Arc::new(indexed_circuit),
                circuit_commitment_randomness,
                circuit_verifying_key: circuit_verifying_key.clone(),
                committer_key: Arc::new(committer_key),
            };
            circuit_keys.push((circuit_proving_key, circuit_verifying_key));
        }

        end_timer!(index_time);
        Ok(circuit_keys)
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn circuit_setup<C: ConstraintSynthesizer<E::Fr>>(
        universal_srs: &UniversalSRS<E>,
        circuit: &C,
    ) -> Result<(CircuitProvingKey<E, MM>, CircuitVerifyingKey<E, MM>), SNARKError> {
        let mut circuit_keys = Self::batch_circuit_setup(universal_srs, &[circuit])?;
        assert_eq!(circuit_keys.len(), 1);
        Ok(circuit_keys.pop().unwrap())
    }

    fn terminate(terminator: &AtomicBool) -> Result<(), MarlinError> {
        if terminator.load(Ordering::Relaxed) { Err(MarlinError::Terminated) } else { Ok(()) }
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

    fn absorb_labeled_with_msg(
        comms: &[LabeledCommitment<Commitment<E>>],
        message: &prover::ThirdMessage<E::Fr>,
        sponge: &mut FS,
    ) {
        let commitments: Vec<_> = comms.iter().map(|c| *c.commitment()).collect();
        Self::absorb_with_msg(&commitments, message, sponge)
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

    fn absorb_with_msg(commitments: &[Commitment<E>], msg: &prover::ThirdMessage<E::Fr>, sponge: &mut FS) {
        let sponge_time = start_timer!(|| "Absorbing commitments and message");
        Self::absorb(commitments, sponge);
        for sum in msg.sums.iter() {
            sponge.absorb_nonnative_field_elements([sum.sum_a, sum.sum_b, sum.sum_c]);
        }
        end_timer!(sponge_time);
    }
}

impl<E: PairingEngine, FS, MM> SNARK for MarlinSNARK<E, FS, MM>
where
    E::Fr: PrimeField,
    E::Fq: PrimeField,
    FS: AlgebraicSponge<E::Fq, 2>,
    MM: MarlinMode,
{
    type BaseField = E::Fq;
    type Certificate = Certificate<E>;
    type FSParameters = FS::Parameters;
    type FiatShamirRng = FS;
    type Proof = Proof<E>;
    type ProvingKey = CircuitProvingKey<E, MM>;
    type ScalarField = E::Fr;
    type UniversalSetupConfig = usize;
    type UniversalSetupParameters = UniversalSRS<E>;
    type VerifierInput = [E::Fr];
    type VerifyingKey = CircuitVerifyingKey<E, MM>;

    fn universal_setup(max_degree: &Self::UniversalSetupConfig) -> Result<Self::UniversalSetupParameters, SNARKError> {
        let setup_time = start_timer!(|| { format!("Marlin::UniversalSetup with max_degree {max_degree}",) });

        let srs = SonicKZG10::<E, FS>::load_srs(*max_degree).map_err(Into::into);
        end_timer!(setup_time);
        srs
    }

    fn setup<C: ConstraintSynthesizer<E::Fr>>(
        circuit: &C,
        srs: &mut SRS<Self::UniversalSetupParameters>,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError> {
        match srs {
            SRS::CircuitSpecific => Self::circuit_specific_setup(circuit),
            SRS::Universal(srs) => Self::circuit_setup(srs, circuit),
        }
        .map_err(SNARKError::from)
    }

    /// Prove that the verifying key indeed includes a part of the reference string,
    /// as well as the indexed circuit (i.e. the circuit as a set of linear-sized polynomials).
    fn prove_vk(
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
        for (poly, &c) in proving_key.circuit.iter().zip(linear_combination_challenges) {
            lc.add(c, poly.label());
        }

        let circuit_id = std::iter::once(&verifying_key.id);
        let query_set = QuerySet::from_iter([("circuit_check".into(), ("challenge".into(), point))]);
        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_id).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, c))
            .collect::<Vec<_>>();

        let committer_key = CommitterUnionKey::union(std::iter::once(proving_key.committer_key.as_ref()));

        let certificate = SonicKZG10::<E, FS>::open_combinations(
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
        fs_parameters: &Self::FSParameters,
        circuit: &C,
        verifying_key: &Self::VerifyingKey,
        certificate: &Self::Certificate,
    ) -> Result<bool, SNARKError> {
        let circuit_id = &verifying_key.id;
        let info = AHPForR1CS::<E::Fr, MM>::index_polynomial_info(std::iter::once(circuit_id));
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
        for ((label, &c), eval) in info.keys().zip_eq(linear_combination_challenges).zip_eq(evaluations_at_point) {
            lc.add(c, label.as_str());
            evaluation += c * eval;
        }

        let query_set = QuerySet::from_iter([("circuit_check".into(), ("challenge".into(), point))]);
        let commitments = verifying_key
            .iter()
            .cloned()
            .zip_eq(info.values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, c))
            .collect::<Vec<_>>();
        let evaluations = Evaluations::from_iter([(("circuit_check".into(), point), evaluation)]);

        let verifier_key = VerifierUnionKey::union(std::iter::once(&verifying_key.verifier_key));

        SonicKZG10::<E, FS>::check_combinations(
            &verifier_key,
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
    fn prove_batch_with_terminator<C: ConstraintSynthesizer<E::Fr>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        keys_to_constraints: &BTreeMap<&CircuitProvingKey<E, MM>, &[&C]>,
        terminator: &AtomicBool,
        zk_rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        if keys_to_constraints.is_empty() {
            return Err(SNARKError::EmptyBatch);
        }

        Self::terminate(terminator)?;

        let mut circuits_to_constraints = BTreeMap::new();
        for (pk, constraints) in keys_to_constraints {
            circuits_to_constraints.insert(pk.circuit.deref(), *constraints);
        }
        let prover_state = AHPForR1CS::<_, MM>::init_prover(&circuits_to_constraints)?;

        // extract information from the prover key and state to consume in further calculations
        let mut batch_sizes = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut total_instances = 0;
        let mut public_inputs = BTreeMap::new(); // inputs need to live longer than the rest of prover_state
        let mut circuit_ids = Vec::with_capacity(keys_to_constraints.len());
        for pk in keys_to_constraints.keys() {
            let batch_size = prover_state.batch_size(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let public_input = prover_state.public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let padded_public_input =
                prover_state.padded_public_inputs(&pk.circuit).ok_or(SNARKError::CircuitNotFound)?;
            let circuit_id = pk.circuit.id;
            batch_sizes.insert(circuit_id, batch_size);
            circuit_infos.insert(circuit_id, &pk.circuit_verifying_key.circuit_info);
            inputs_and_batch_sizes.insert(circuit_id, (batch_size, padded_public_input));
            total_instances += batch_size;
            public_inputs.insert(circuit_id, public_input);
            circuit_ids.push(circuit_id);
        }
        assert_eq!(prover_state.total_instances, total_instances);

        let committer_key = CommitterUnionKey::union(keys_to_constraints.keys().map(|pk| pk.committer_key.deref()));

        let circuit_commitments =
            keys_to_constraints.keys().map(|pk| pk.circuit_verifying_key.circuit_commitments.as_slice());

        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round

        Self::terminate(terminator)?;
        let mut prover_state = AHPForR1CS::<_, MM>::prover_first_round(prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_commitments, first_commitment_randomnesses) = {
            let first_round_oracles = Arc::get_mut(prover_state.first_round_oracles.as_mut().unwrap()).unwrap();
            SonicKZG10::<E, FS>::commit(&committer_key, first_round_oracles.iter_for_commit(), Some(zk_rng))?
        };
        end_timer!(first_round_comm_time);

        Self::absorb_labeled(&first_commitments, &mut sponge);
        Self::terminate(terminator)?;

        let (verifier_first_message, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            prover_state.max_constraint_domain,
            prover_state.max_non_zero_domain,
            &mut sponge,
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
            &committer_key,
            second_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(second_round_comm_time);

        Self::absorb_labeled(&second_commitments, &mut sponge);
        Self::terminate(terminator)?;

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_second_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        Self::terminate(terminator)?;

        let (prover_third_message, third_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_commitments, third_commitment_randomnesses) = SonicKZG10::<E, FS>::commit_with_terminator(
            &committer_key,
            third_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(third_round_comm_time);

        Self::absorb_labeled_with_msg(&third_commitments, &prover_third_message, &mut sponge);

        let (verifier_third_msg, verifier_state) =
            AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round

        Self::terminate(terminator)?;

        let first_round_oracles = Arc::clone(prover_state.first_round_oracles.as_ref().unwrap());
        let fourth_oracles = AHPForR1CS::<_, MM>::prover_fourth_round(verifier_third_msg, prover_state, zk_rng)?;
        Self::terminate(terminator)?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_commitments, fourth_commitment_randomnesses) = SonicKZG10::<E, FS>::commit_with_terminator(
            &committer_key,
            fourth_oracles.iter().map(Into::into),
            terminator,
            Some(zk_rng),
        )?;
        end_timer!(fourth_round_comm_time);

        Self::absorb_labeled(&fourth_commitments, &mut sponge);

        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        // --------------------------------------------------------------------

        Self::terminate(terminator)?;

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = keys_to_constraints
            .keys()
            .flat_map(|pk| pk.circuit.iter())
            .chain(first_round_oracles.iter_for_open())
            .chain(second_oracles.iter())
            .chain(third_oracles.iter())
            .chain(fourth_oracles.iter())
            .collect();
        assert!(
            polynomials.len()
                == keys_to_constraints.len() * 12 + // polys for row, col, rowcol, val
            AHPForR1CS::<E::Fr, MM>::num_first_round_oracles(total_instances) +
            AHPForR1CS::<E::Fr, MM>::num_second_round_oracles() +
            AHPForR1CS::<E::Fr, MM>::num_third_round_oracles(keys_to_constraints.len()) +
            AHPForR1CS::<E::Fr, MM>::num_fourth_round_oracles()
        );

        Self::terminate(terminator)?;

        // Gather commitments in one vector.
        let witness_commitments = first_commitments.chunks_exact(3);
        let mask_poly = MM::ZK.then(|| *witness_commitments.remainder()[0].commitment());
        let witness_commitments = witness_commitments
            .map(|c| proof::WitnessCommitments {
                w: *c[0].commitment(),
                z_a: *c[1].commitment(),
                z_b: *c[2].commitment(),
            })
            .collect();
        let third_commitments_chunked = third_commitments.chunks_exact(3);

        #[rustfmt::skip]
        let commitments = proof::Commitments {
            witness_commitments,
            mask_poly,

            g_1: *second_commitments[0].commitment(),
            h_1: *second_commitments[1].commitment(),

            g_a_commitments: third_commitments_chunked.clone().map(|c| *c[0].commitment()).collect(),
            g_b_commitments: third_commitments_chunked.clone().map(|c| *c[1].commitment()).collect(),
            g_c_commitments: third_commitments_chunked.map(|c| *c[2].commitment()).collect(),

            h_2: *fourth_commitments[0].commitment(),
        };

        let labeled_commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_ids.iter()).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments.into_iter())
            .chain(second_commitments.into_iter())
            .chain(third_commitments.into_iter())
            .chain(fourth_commitments.into_iter())
            .collect();

        // Gather commitment randomness together.
        let commitment_randomnesses: Vec<Randomness<E>> = keys_to_constraints
            .keys()
            .flat_map(|pk| pk.circuit_commitment_randomness.clone())
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
            &public_inputs,
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

        let evaluations = proof::Evaluations::from_map(&evaluations, batch_sizes.clone());
        end_timer!(eval_time);

        Self::terminate(terminator)?;

        sponge.absorb_nonnative_field_elements(evaluations.to_field_elements());

        let pc_proof = SonicKZG10::<E, FS>::open_combinations(
            &committer_key,
            lc_s.values(),
            polynomials,
            &labeled_commitments,
            &query_set.to_set(),
            &commitment_randomnesses,
            &mut sponge,
        )?;

        Self::terminate(terminator)?;

        let proof = Proof::<E>::new(batch_sizes, commitments, evaluations, prover_third_message, pc_proof)?;
        assert_eq!(proof.pc_proof.is_hiding(), MM::ZK);

        // Collect verification key and public inputs to verify_batch
        let mut vk_to_inputs = BTreeMap::new();
        for pk in keys_to_constraints.keys() {
            vk_to_inputs.insert(&pk.circuit_verifying_key, public_inputs.get(&pk.circuit.id).unwrap().as_slice());
        }

        #[cfg(debug_assertions)]
        if !Self::verify_batch(fs_parameters, &vk_to_inputs, &proof)? {
            println!("Invalid proof")
        }
        end_timer!(prover_time);

        Ok(proof)
    }

    /// This is the main entrypoint for verifying proofs.
    /// You can find a specification of the verifier algorithm in:
    /// https://github.com/AleoHQ/protocol-docs/tree/main/marlin
    fn verify_batch_prepared<B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        keys_to_inputs: &BTreeMap<<Self::VerifyingKey as PrepareOrd>::Prepared, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        if keys_to_inputs.is_empty() {
            return Err(SNARKError::EmptyBatch);
        }

        let batch_sizes_vec = proof.batch_sizes()?;
        let mut batch_sizes = BTreeMap::new();
        for (i, (vk, public_inputs_i)) in keys_to_inputs.iter().enumerate() {
            batch_sizes.insert(vk.orig_vk.id, batch_sizes_vec[i]);

            if public_inputs_i.is_empty() {
                return Err(SNARKError::EmptyBatch);
            }

            if public_inputs_i.len() != batch_sizes_vec[i] {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }

        // collect values into structures for our calculations
        let mut max_constraint_domain = None;
        let mut max_non_zero_domain = None;
        let mut public_inputs = BTreeMap::new();
        let mut padded_public_vec = Vec::with_capacity(keys_to_inputs.len());
        let mut inputs_and_batch_sizes = BTreeMap::new();
        let mut input_domains = BTreeMap::new();
        let mut circuit_infos = BTreeMap::new();
        let mut vks = Vec::with_capacity(keys_to_inputs.len());
        let mut circuit_ids = Vec::with_capacity(keys_to_inputs.len());
        for (vk, public_inputs_i) in keys_to_inputs.iter() {
            vks.push(&vk.orig_vk.verifier_key);

            let constraint_domains =
                AHPForR1CS::<_, MM>::max_constraint_domain(&vk.orig_vk.circuit_info, max_constraint_domain)?;
            max_constraint_domain = constraint_domains.max_constraint_domain;
            let non_zero_domains =
                AHPForR1CS::<_, MM>::max_non_zero_domain(&vk.orig_vk.circuit_info, max_non_zero_domain)?;
            max_non_zero_domain = non_zero_domains.max_non_zero_domain;

            let input_domain = EvaluationDomain::<E::Fr>::new(vk.orig_vk.circuit_info.num_public_inputs).unwrap();
            input_domains.insert(vk.orig_vk.id, input_domain);

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
            let circuit_id = vk.orig_vk.id;
            public_inputs.insert(circuit_id, parsed_public_inputs_i);
            padded_public_vec.push(padded_public_inputs_i);
            circuit_infos.insert(circuit_id, &vk.orig_vk.circuit_info);
            circuit_ids.push(circuit_id);
        }
        for (i, (vk, &batch_size)) in keys_to_inputs.keys().zip(batch_sizes.values()).enumerate() {
            inputs_and_batch_sizes.insert(vk.orig_vk.id, (batch_size, padded_public_vec[i].as_slice()));
        }

        let verifier_key = VerifierUnionKey::<E>::union(vks);

        let comms = &proof.commitments;
        let proof_has_correct_zk_mode = if MM::ZK {
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

        let verifier_time = start_timer!(|| format!("Marlin::Verify with batch sizes: {:?}", batch_sizes));

        let first_round_info = AHPForR1CS::<E::Fr, MM>::first_round_polynomial_info(batch_sizes.iter());

        let mut first_comms_consumed = 0;
        let mut first_commitments = batch_sizes
            .iter()
            .flat_map(|(&circuit_id, &batch_size)| {
                let first_comms = comms.witness_commitments[first_comms_consumed..][..batch_size]
                    .iter()
                    .enumerate()
                    .flat_map(|(j, w_comm)| {
                        [
                            LabeledCommitment::new_with_info(
                                &first_round_info[&witness_label(circuit_id, "w", j)],
                                w_comm.w,
                            ),
                            LabeledCommitment::new_with_info(
                                &first_round_info[&witness_label(circuit_id, "z_a", j)],
                                w_comm.z_a,
                            ),
                            LabeledCommitment::new_with_info(
                                &first_round_info[&witness_label(circuit_id, "z_b", j)],
                                w_comm.z_b,
                            ),
                        ]
                    })
                    .collect_vec();
                first_comms_consumed += batch_size;
                first_comms
            })
            .collect_vec();

        if MM::ZK {
            first_commitments.push(LabeledCommitment::new_with_info(
                first_round_info.get("mask_poly").unwrap(),
                comms.mask_poly.unwrap(),
            ));
        }

        let second_round_info =
            AHPForR1CS::<E::Fr, MM>::second_round_polynomial_info(max_constraint_domain.unwrap().size());
        let second_commitments = [
            LabeledCommitment::new_with_info(&second_round_info["g_1"], comms.g_1),
            LabeledCommitment::new_with_info(&second_round_info["h_1"], comms.h_1),
        ];

        let third_round_info = AHPForR1CS::<E::Fr, MM>::third_round_polynomial_info(circuit_infos.clone().into_iter());
        let third_commitments = comms
            .g_a_commitments
            .iter()
            .zip_eq(comms.g_b_commitments.iter())
            .zip_eq(comms.g_c_commitments.iter())
            .zip_eq(circuit_ids.iter())
            .flat_map(|(((g_a, g_b), g_c), circuit_id)| {
                [
                    LabeledCommitment::new_with_info(&third_round_info[&witness_label(*circuit_id, "g_a", 0)], *g_a),
                    LabeledCommitment::new_with_info(&third_round_info[&witness_label(*circuit_id, "g_b", 0)], *g_b),
                    LabeledCommitment::new_with_info(&third_round_info[&witness_label(*circuit_id, "g_c", 0)], *g_c),
                ]
            })
            .collect_vec();

        let fourth_round_info = AHPForR1CS::<E::Fr, MM>::fourth_round_polynomial_info();
        let fourth_commitments = [LabeledCommitment::new_with_info(&fourth_round_info["h_2"], comms.h_2)];

        let circuit_commitments = keys_to_inputs.keys().map(|vk| vk.orig_vk.circuit_commitments.as_slice());
        let mut sponge = Self::init_sponge(fs_parameters, &inputs_and_batch_sizes, circuit_commitments.clone());

        // --------------------------------------------------------------------
        // First round
        let first_round_time = start_timer!(|| "First round");
        Self::absorb_labeled(&first_commitments, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_first_round(
            &batch_sizes,
            &circuit_infos,
            max_constraint_domain.unwrap(),
            max_non_zero_domain.unwrap(),
            &mut sponge,
        )?;
        end_timer!(first_round_time);
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

        Self::absorb_labeled_with_msg(&third_commitments, &proof.msg, &mut sponge);
        let (_, verifier_state) = AHPForR1CS::<_, MM>::verifier_third_round(verifier_state, &mut sponge)?;
        end_timer!(third_round_time);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Fourth round
        let fourth_round_time = start_timer!(|| "Fourth round");

        Self::absorb_labeled(&fourth_commitments, &mut sponge);
        let verifier_state = AHPForR1CS::<_, MM>::verifier_fourth_round(verifier_state, &mut sponge)?;
        end_timer!(fourth_round_time);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.

        // Gather commitments in one vector.
        let commitments: Vec<_> = circuit_commitments
            .into_iter()
            .flatten()
            .zip_eq(AHPForR1CS::<E::Fr, MM>::index_polynomial_info(circuit_ids.iter()).values())
            .map(|(c, info)| LabeledCommitment::new_with_info(info, *c))
            .chain(first_commitments)
            .chain(second_commitments)
            .chain(third_commitments)
            .chain(fourth_commitments)
            .collect();

        let query_set_time = start_timer!(|| "Constructing query set");
        let (query_set, verifier_state) = AHPForR1CS::<_, MM>::verifier_query_set(verifier_state);
        end_timer!(query_set_time);

        sponge.absorb_nonnative_field_elements(proof.evaluations.to_field_elements());

        let mut evaluations = Evaluations::new();

        let mut current_circuit_id = "".to_string();
        let mut circuit_index: i64 = -1;
        for (label, (_point_name, q)) in query_set.to_set() {
            if AHPForR1CS::<E::Fr, MM>::LC_WITH_ZERO_EVAL.contains(&label.as_ref()) {
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
        let lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_inputs,
            &evaluations,
            &proof.msg,
            &verifier_state,
        )?;
        end_timer!(lc_time);

        let pc_time = start_timer!(|| "Checking linear combinations with PC");
        let evaluations_are_correct = SonicKZG10::<E, FS>::check_combinations(
            &verifier_key,
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
            eprintln!("SonicKZG10::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " SonicKZG10::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct & proof_has_correct_zk_mode
        ));
        Ok(evaluations_are_correct & proof_has_correct_zk_mode)
    }
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::{
        crypto_hash::PoseidonSponge,
        snark::marlin::{MarlinHidingMode, MarlinSNARK, TestCircuit},
        AlgebraicSponge,
        SRS,
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::{TestRng, Uniform};

    use core::ops::MulAssign;

    const ITERATIONS: usize = 10;

    type FS = PoseidonSponge<Fq, 2, 1>;
    type TestSNARK = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;

    #[test]
    fn marlin_snark_test() {
        let mut rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Construct the circuit.

            let a = Fr::rand(&mut rng);
            let b = Fr::rand(&mut rng);
            let mut c = a;
            c.mul_assign(&b);

            let mul_depth = 1;
            let num_constraints = 100;
            let num_variables = 25;
            let (circ, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

            // Generate the circuit parameters.

            let (pk, vk) = TestSNARK::setup(&circ, &mut SRS::CircuitSpecific).unwrap();

            // Test native proof and verification.
            let fs_parameters = FS::sample_parameters();

            let proof = TestSNARK::prove(&fs_parameters, &pk, &circ, &mut rng).unwrap();

            assert!(
                TestSNARK::verify(&fs_parameters, &vk.clone(), public_inputs.as_slice(), &proof).unwrap(),
                "The native verification check fails."
            );
        }
    }
}
