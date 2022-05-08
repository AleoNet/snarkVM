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

use crate::errors::SNARKError;
use snarkvm_utilities::{FromBytes, ToBytes, ToMinimalBits};

use rand::{CryptoRng, Rng};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_r1cs::ConstraintSynthesizer;
use std::{borrow::Borrow, fmt::Debug, sync::atomic::AtomicBool};

/// Defines a trait that describes preparing from an unprepared version to a prepare version.
pub trait Prepare {
    type Prepared;
    fn prepare(&self) -> Self::Prepared;
}

/// An abstraction layer to enable a circuit-specific SRS or universal SRS.
/// Forward compatible with future assumptions that proof systems will require.
pub enum SRS<'a, R: Rng + CryptoRng, T> {
    CircuitSpecific(&'a mut R),
    Universal(&'a T),
}

pub trait SNARK {
    type ScalarField: Clone + PrimeField;
    type BaseField: Clone + PrimeField;

    type Proof: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Send + Sync;
    type ProvingKey: Clone + ToBytes + FromBytes + Send + Sync;

    // We can specify their defaults to `()` when `associated_type_defaults` feature becomes stable in Rust
    type UniversalSetupConfig: Clone;
    type UniversalSetupParameters: FromBytes + ToBytes + Clone;

    type VerifierInput: ?Sized;
    type VerifyingKey: Clone
        + Send
        + Sync
        + ToBytes
        + FromBytes
        + Prepare
        + for<'a> From<&'a Self::ProvingKey>
        + From<Self::ProvingKey>
        + ToConstraintField<Self::BaseField>
        + ToMinimalBits;

    fn universal_setup<R: Rng + CryptoRng>(
        config: &Self::UniversalSetupConfig,
        rng: &mut R,
    ) -> Result<Self::UniversalSetupParameters, SNARKError>;

    fn setup<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        circuit: &C,
        srs: &mut SRS<R, Self::UniversalSetupParameters>,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError>;

    fn prove_batch<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &[C],
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        Self::prove_batch_with_terminator(proving_key, input_and_witness, &AtomicBool::new(false), rng)
    }

    fn prove<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        Self::prove_batch(proving_key, std::slice::from_ref(input_and_witness), rng)
    }

    fn prove_batch_with_terminator<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &[C],
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError>;

    fn prove_with_terminator<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        Self::prove_batch_with_terminator(proving_key, std::slice::from_ref(input_and_witness), terminator, rng)
    }

    fn verify_batch_prepared<B: Borrow<Self::VerifierInput>>(
        prepared_verifying_key: &<Self::VerifyingKey as Prepare>::Prepared,
        input: &[B],
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError>;

    fn verify_batch<B: Borrow<Self::VerifierInput>>(
        verifying_key: &Self::VerifyingKey,
        input: &[B],
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let processed_verifying_key = verifying_key.prepare();
        Self::verify_batch_prepared(&processed_verifying_key, input, proof)
    }

    fn verify<B: Borrow<Self::VerifierInput>>(
        verifying_key: &Self::VerifyingKey,
        input: B,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        Self::verify_batch(verifying_key, &[input], proof)
    }
}
