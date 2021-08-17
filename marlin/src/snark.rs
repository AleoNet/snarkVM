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

//! The Marlin zkSNARK implementation
use crate::{
    fiat_shamir::FiatShamirChaChaRng,
    marlin::{CircuitProvingKey, CircuitVerifyingKey, MarlinSNARK, MarlinTestnet1Mode, Proof, UniversalSRS},
    Parameters,
};
use snarkvm_algorithms::{errors::SNARKError, traits::SNARK};
use snarkvm_curves::traits::PairingEngine;
use snarkvm_fields::ToConstraintField;
use snarkvm_profiler::{end_timer, start_timer};
use snarkvm_r1cs::ConstraintSynthesizer;

pub use snarkvm_polycommit::{marlin_pc::MarlinKZG10 as MultiPC, PolynomialCommitment};

use blake2::Blake2s;
use core::marker::PhantomData;
use rand_core::RngCore;
use std::sync::atomic::AtomicBool;

/// A structured reference string which will be used to derive a circuit-specific
/// common reference string
pub type SRS<E> = UniversalSRS<<E as PairingEngine>::Fr, MultiPC<E>>;

/// Type alias for a Marlin instance using the KZG10 polynomial commitment and Blake2s
pub type Marlin<E> = MarlinSystem<<E as PairingEngine>::Fr, MultiPC<E>, Blake2s>;

/// A circuit-specific proving key.
pub type ProvingKey<E> = CircuitProvingKey<<E as PairingEngine>::Fr, MultiPC<E>>;

/// A circuit-specific verifying key.
pub type VerifyingKey<E> = CircuitVerifyingKey<<E as PairingEngine>::Fr, MultiPC<E>>;

impl<E: PairingEngine> From<Parameters<E>> for VerifyingKey<E> {
    fn from(parameters: Parameters<E>) -> Self {
        parameters.verifying_key
    }
}

/// The Marlin proof system for testnet1.
pub type MarlinTestnet1<E> = MarlinSNARK<
    <E as PairingEngine>::Fr,
    <E as PairingEngine>::Fq,
    MultiPC<E>,
    FiatShamirChaChaRng<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, Blake2s>,
    MarlinTestnet1Mode,
>;

/// A Marlin instance using the KZG10 polynomial commitment and Blake2s
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarlinSystem<E, C, V>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    V: ToConstraintField<E::Fr>,
    <MultiPC<E> as PolynomialCommitment<E::Fr>>::Commitment: ToConstraintField<E::Fq>,
    <MultiPC<E> as PolynomialCommitment<E::Fr>>::VerifierKey: ToConstraintField<E::Fq>,
{
    _engine: PhantomData<E>,
    _circuit: PhantomData<C>,
    _verifier_input: PhantomData<V>,
}

impl<E, C, V> SNARK for MarlinSystem<E, C, V>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    V: ToConstraintField<E::Fr>,
    <MultiPC<E> as PolynomialCommitment<E::Fr>>::Commitment: ToConstraintField<E::Fq>,
    <MultiPC<E> as PolynomialCommitment<E::Fr>>::VerifierKey: ToConstraintField<E::Fq>,
{
    type AllocatedCircuit = C;
    type Circuit = (C, SRS<E>);
    // Abuse the Circuit type to pass the SRS as well.
    type PreparedVerifyingKey = VerifyingKey<E>;
    type Proof = Proof<<E as PairingEngine>::Fr, MultiPC<E>>;
    type ProvingKey = Parameters<E>;
    type VerifierInput = V;
    type VerifyingKey = VerifyingKey<E>;

    fn setup<R: RngCore>(
        (circuit, srs): &Self::Circuit,
        _rng: &mut R, // The Marlin circuit setup is deterministic.
    ) -> Result<(Self::ProvingKey, Self::PreparedVerifyingKey), SNARKError> {
        let setup_time = start_timer!(|| "{Marlin}::Setup");
        let parameters = Parameters::<E>::new(circuit, srs)?;
        end_timer!(setup_time);

        let verifying_key = parameters.verifying_key.clone();
        Ok((parameters, verifying_key))
    }

    fn prove_with_terminator<R: RngCore>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &Self::AllocatedCircuit,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let proving_time = start_timer!(|| "{Marlin}::Proving");
        let proof =
            MarlinTestnet1::<E>::prove_with_terminator(&proving_key.proving_key, input_and_witness, terminator, rng)
                .map_err(|error| error.into_snark_error("Failed to generate proof"))?;
        end_timer!(proving_time);
        Ok(proof)
    }

    fn verify(
        verifying_key: &Self::PreparedVerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let verification_time = start_timer!(|| "{Marlin}::Verifying");
        let res = MarlinTestnet1::<E>::verify(&verifying_key, &input.to_field_elements()?, &proof)
            .map_err(|error| error.into_snark_error("Could not verify proof"))?;
        end_timer!(verification_time);

        Ok(res)
    }
}
