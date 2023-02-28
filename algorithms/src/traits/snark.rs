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

use crate::{errors::SNARKError, AlgebraicSponge, snark::marlin::{Circuit, MarlinMode}};
use snarkvm_utilities::{CanonicalDeserialize, CanonicalSerialize, FromBytes, ToBytes, ToMinimalBits};

use rand::{CryptoRng, Rng};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_r1cs::ConstraintSynthesizer;
use std::{borrow::Borrow, collections::BTreeMap, fmt::Debug, sync::atomic::AtomicBool};

/// Defines a trait that describes preparing from an unprepared version to a prepare version.
pub trait Prepare {
    type Prepared;
    fn prepare(&self) -> Self::Prepared;
}

/// An abstraction layer to enable a circuit-specific SRS or universal SRS.
/// Forward compatible with future assumptions that proof systems will require.
pub enum SRS<'a, T> {
    CircuitSpecific,
    Universal(&'a T),
}

pub trait SNARK {
    type ScalarField: Clone + PrimeField;
    type BaseField: Clone + PrimeField;

    /// A certificate that the indexing was performed correctly.
    type Certificate: CanonicalSerialize
        + CanonicalDeserialize
        + Clone
        + Debug
        + ToBytes
        + FromBytes
        + PartialEq
        + Eq
        + Send
        + Sync;
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

    type FiatShamirRng: AlgebraicSponge<Self::BaseField, 2, Parameters = Self::FSParameters>;
    type FSParameters;
    type MM: MarlinMode;

    fn universal_setup(config: &Self::UniversalSetupConfig) -> Result<Self::UniversalSetupParameters, SNARKError>;

    fn setup<C: ConstraintSynthesizer<Self::ScalarField>>(
        circuit: &C,
        srs: &mut SRS<Self::UniversalSetupParameters>,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError>;

    fn prove_vk(
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        proving_key: &Self::ProvingKey,
    ) -> Result<Self::Certificate, SNARKError>;

    fn prove_batch<'a, C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        proving_key: &Self::ProvingKey,
        input_and_witness: &BTreeMap<&'a Circuit<Self::ScalarField, Self::MM>, &[C]>,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        Self::prove_batch_with_terminator(fs_parameters, proving_key, input_and_witness, &AtomicBool::new(false), rng)
    }

    fn prove<'a, C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        circuit: &'a Circuit<Self::ScalarField, Self::MM>,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let input_and_witnesses = BTreeMap::new();
        input_and_witnesses.insert(circuit, vec![*input_and_witness].as_slice());
        Self::prove_batch(fs_parameters, proving_key, &input_and_witnesses, rng)
    }

    fn prove_batch_with_terminator<'a, C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        proving_key: &Self::ProvingKey,
        input_and_witness: &BTreeMap<&'a Circuit<Self::ScalarField, Self::MM>, &[C]>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError>;

    fn prove_with_terminator<'a, C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        circuit: &'a Circuit<Self::ScalarField, Self::MM>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let input_and_witnesses = BTreeMap::new();
        input_and_witnesses.insert(circuit, vec![*input_and_witness].as_slice());
        Self::prove_batch_with_terminator(
            fs_parameters,
            proving_key,
            &input_and_witnesses,
            terminator,
            rng,
        )
    }

    fn verify_vk<C: ConstraintSynthesizer<Self::ScalarField>>(
        fs_parameters: &Self::FSParameters,
        circuit: &C,
        verifying_key: &Self::VerifyingKey,
        certificate: &Self::Certificate,
    ) -> Result<bool, SNARKError>;

    fn verify_batch_prepared<'a, B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        prepared_verifying_key: &<Self::VerifyingKey as Prepare>::Prepared,
        input: &BTreeMap<&'a Circuit<Self::ScalarField, Self::MM>, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError>;

    fn verify_batch<'a, B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        inputs: &BTreeMap<&'a Circuit<Self::ScalarField, Self::MM>, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let preparation_time = start_timer!(|| "Preparing vk");
        let processed_verifying_key = verifying_key.prepare();
        end_timer!(preparation_time);
        Self::verify_batch_prepared(fs_parameters, &processed_verifying_key, inputs, proof)
    }

    fn verify<'a, B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        input: B,
        circuit: &'a Circuit<Self::ScalarField, Self::MM>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let inputs = BTreeMap::new();
        inputs.insert(circuit, vec![input].as_slice());
        Self::verify_batch(fs_parameters, verifying_key, &inputs, proof)
    }
}
