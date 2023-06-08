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

use crate::{errors::SNARKError, AlgebraicSponge};
use snarkvm_utilities::{CanonicalDeserialize, CanonicalSerialize, FromBytes, ToBytes, ToMinimalBits};

use rand::{CryptoRng, Rng};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_r1cs::ConstraintSynthesizer;
use std::{borrow::Borrow, collections::BTreeMap, fmt::Debug};

/// Defines trait that describes preparing from an unprepared version to a prepare version.
pub trait Prepare {
    type Prepared;
    fn prepare(&self) -> Self::Prepared;
}

/// Defines trait that describes preparing from an unprepared version to an orderable prepare version.
pub trait PrepareOrd {
    // NOTE: we keep this separate from Prepare because we also have unordered Prepared types
    type Prepared: Ord;
    fn prepare(&self) -> Self::Prepared;
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
    type ProvingKey: Clone + ToBytes + FromBytes + Send + Sync + Ord;

    // We can specify their defaults to `()` when `associated_type_defaults` feature becomes stable in Rust
    type UniversalSetupConfig: Clone;
    type UniversalSetupParameters: FromBytes + ToBytes + Clone;

    type VerifierInput: ?Sized;
    type VerifyingKey: Clone
        + Send
        + Sync
        + ToBytes
        + FromBytes
        + PrepareOrd
        + for<'a> From<&'a Self::ProvingKey>
        + From<Self::ProvingKey>
        + ToConstraintField<Self::BaseField>
        + ToMinimalBits
        + Ord;

    type FiatShamirRng: AlgebraicSponge<Self::BaseField, 2, Parameters = Self::FSParameters>;
    type FSParameters;

    fn universal_setup(config: &Self::UniversalSetupConfig) -> Result<Self::UniversalSetupParameters, SNARKError>;

    fn circuit_setup<C: ConstraintSynthesizer<Self::ScalarField>>(
        srs: &Self::UniversalSetupParameters,
        circuit: &C,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError>;

    fn prove_vk(
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        proving_key: &Self::ProvingKey,
    ) -> Result<Self::Certificate, SNARKError>;

    fn prove<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        proving_key: &Self::ProvingKey,
        constraints: &C,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let mut keys_to_constraints = BTreeMap::new();
        keys_to_constraints.insert(proving_key, std::slice::from_ref(constraints));
        Self::prove_batch(fs_parameters, &keys_to_constraints, rng)
    }

    fn prove_batch<C: ConstraintSynthesizer<Self::ScalarField>, R: Rng + CryptoRng>(
        fs_parameters: &Self::FSParameters,
        keys_to_constraints: &BTreeMap<&Self::ProvingKey, &[C]>,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError>;

    fn verify_vk<C: ConstraintSynthesizer<Self::ScalarField>>(
        fs_parameters: &Self::FSParameters,
        circuit: &C,
        verifying_key: &Self::VerifyingKey,
        certificate: &Self::Certificate,
    ) -> Result<bool, SNARKError>;

    fn verify<B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        verifying_key: &Self::VerifyingKey,
        input: B,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let mut keys_to_inputs = BTreeMap::new();
        let inputs = [input];
        keys_to_inputs.insert(verifying_key, &inputs[..]);
        Self::verify_batch(fs_parameters, &keys_to_inputs, proof)
    }

    fn verify_batch<B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        keys_to_inputs: &BTreeMap<&Self::VerifyingKey, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let preparation_time = start_timer!(|| "Preparing vks");
        let prepared_keys_to_inputs = keys_to_inputs
            .iter()
            .map(|(key, inputs)| {
                let prepared_key = key.prepare();
                (prepared_key, *inputs)
            })
            .collect::<BTreeMap<<Self::VerifyingKey as PrepareOrd>::Prepared, &[B]>>();
        end_timer!(preparation_time);
        Self::verify_batch_prepared(fs_parameters, &prepared_keys_to_inputs, proof)
    }

    fn verify_batch_prepared<B: Borrow<Self::VerifierInput>>(
        fs_parameters: &Self::FSParameters,
        keys_to_inputs: &BTreeMap<<Self::VerifyingKey as PrepareOrd>::Prepared, &[B]>,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError>;
}
