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

use crate::errors::SNARKError;
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::{CryptoRng, Rng};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_r1cs::ConstraintSynthesizer;
use std::fmt::Debug;

/// Defines a trait that describes preparing from an unprepared version to a prepare version.
pub trait Prepare<T> {
    fn prepare(&self) -> T;
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

    type PreparedVerifyingKey: Clone;
    type Proof: Clone + Debug + ToBytes + FromBytes;
    type ProvingKey: Clone + ToBytes + FromBytes;

    // We can specify their defaults to `()` when `associated_type_defaults` feature becomes stable in Rust
    type UniversalSetupConfig: Clone;
    type UniversalSetupParameters: FromBytes + ToBytes + Clone;

    type VerifierInput: ?Sized;
    type VerifyingKey: Clone
        + Send
        + Sync
        + ToBytes
        + FromBytes
        + Prepare<Self::PreparedVerifyingKey>
        + From<Self::PreparedVerifyingKey>
        + From<Self::ProvingKey>
        + ToConstraintField<Self::BaseField>;

    fn universal_setup<R: Rng + CryptoRng>(
        _config: &Self::UniversalSetupConfig,
        _rng: &mut R,
    ) -> Result<Self::UniversalSetupParameters, SNARKError> {
        unimplemented!()
    }

    fn setup<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        circuit: &C,
        srs: &mut SRS<R, Self::UniversalSetupParameters>,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError>;

    fn prove<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError>;

    fn verify_prepared(
        prepared_verifying_key: &Self::PreparedVerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError>;

    fn verify(
        verifying_key: &Self::VerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let processed_verifying_key = verifying_key.prepare();
        Self::verify_prepared(&processed_verifying_key, input, proof)
    }
}
