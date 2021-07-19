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

use core::fmt::Debug;

use snarkvm_algorithms::traits::SNARK;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::Boolean,
    traits::alloc::AllocGadget,
    AllocBytesGadget,
    FromFieldElementsGadget,
    ToBytesGadget,
    ToConstraintFieldGadget,
};

pub trait PrepareGadget<T, F: PrimeField> {
    fn prepare<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<T, SynthesisError>;
}

pub trait SNARKVerifierGadget<S: SNARK> {
    type PreparedVerificationKeyGadget: Clone;
    type VerificationKeyGadget: AllocGadget<S::VerifyingKey, S::BaseField>
        + ToConstraintFieldGadget<S::BaseField>
        + ToBytesGadget<S::BaseField>
        + PrepareGadget<Self::PreparedVerificationKeyGadget, S::BaseField>
        + AllocBytesGadget<Vec<u8>, S::BaseField>;
    type ProofGadget: AllocGadget<S::Proof, S::BaseField> + AllocBytesGadget<Vec<u8>, S::BaseField>;
    type Input: Clone + ?Sized;

    fn check_verify<'a, CS: ConstraintSystem<S::BaseField>, I: Iterator<Item = Self::Input>>(
        cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        input: I,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError>;

    fn prepared_check_verify<'a, CS: ConstraintSystem<S::BaseField>, I: Iterator<Item = Self::Input>>(
        cs: CS,
        prepared_verification_key: &Self::PreparedVerificationKeyGadget,
        input: I,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError>;
}

// TODO (raychu86): Unify with the `SNARK` trait. Currently the `SNARKGadget` is only used for `marlin`.

/// This implements constraints for SNARK verifiers.
pub trait SNARKGadget<S: SNARK> {
    type PreparedVerifyingKeyVar: AllocGadget<S::PreparedVerifyingKey, S::BaseField> + Clone;
    type VerifyingKeyVar: AllocGadget<S::VerifyingKey, S::BaseField> + ToBytesGadget<S::BaseField> + Clone;
    type InputVar: AllocGadget<Vec<S::ScalarField>, S::BaseField>
        + Clone
        + FromFieldElementsGadget<S::ScalarField, S::BaseField>;
    type ProofVar: AllocGadget<S::Proof, S::BaseField> + Clone;

    /// Information about the R1CS constraints required to check proofs relative
    /// a given verification key. In the context of a LPCP-based pairing-based SNARK
    /// like that of [[Groth16]](https://eprint.iacr.org/2016/260),
    /// this is independent of the R1CS matrices,
    /// whereas for more "complex" SNARKs like [[Marlin]](https://eprint.iacr.org/2019/1047),
    /// this can encode information about the highest degree of polynomials
    /// required to verify proofs.
    type VerifierSize: PartialOrd + Clone + Debug;

    /// Returns information about the R1CS constraints required to check proofs relative
    /// to the verification key `circuit_vk`.
    fn verifier_size(circuit_vk: &S::VerifyingKey) -> Self::VerifierSize;

    fn verify_with_processed_vk<CS: ConstraintSystem<S::BaseField>>(
        cs: CS,
        circuit_pvk: &Self::PreparedVerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError>;

    fn verify<CS: ConstraintSystem<S::BaseField>>(
        cs: CS,
        circuit_vk: &Self::VerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError>;
}
