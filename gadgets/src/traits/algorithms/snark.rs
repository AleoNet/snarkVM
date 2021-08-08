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

use snarkvm_algorithms::traits::SNARK;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    traits::alloc::AllocGadget,
    AllocBytesGadget,
    FromFieldElementsGadget,
    MergeGadget,
    ToBitsLEGadget,
    ToBytesGadget,
    ToConstraintFieldGadget,
    ToMinimalBitRepresentationGadget,
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
        + AllocBytesGadget<Vec<u8>, S::BaseField>
        + ToMinimalBitRepresentationGadget<S::BaseField>;
    type ProofGadget: AllocGadget<S::Proof, S::BaseField> + AllocBytesGadget<Vec<u8>, S::BaseField>;
    type InputGadget: Clone
        + AllocGadget<Vec<S::ScalarField>, S::BaseField>
        + ToBitsLEGadget<S::BaseField>
        + FromFieldElementsGadget<S::ScalarField, S::BaseField>
        + MergeGadget<S::BaseField>
        + ?Sized;

    fn check_verify<'a, CS: ConstraintSystem<S::BaseField>>(
        mut cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        input: &Self::InputGadget,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError> {
        let prepared_verification_key = verification_key.prepare(cs.ns(|| "prepare"))?;
        Self::prepared_check_verify(
            cs.ns(|| "prepared verification"),
            &prepared_verification_key,
            input,
            proof,
        )
    }

    fn prepared_check_verify<'a, CS: ConstraintSystem<S::BaseField>>(
        cs: CS,
        prepared_verification_key: &Self::PreparedVerificationKeyGadget,
        input: &Self::InputGadget,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError>;
}
