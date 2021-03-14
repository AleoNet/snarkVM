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

use crate::utilities::{
    alloc::{AllocBytesGadget, AllocGadget},
    ToBitsBEGadget,
    ToBytesGadget,
};
use snarkvm_algorithms::traits::SNARK;
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

pub trait SNARKVerifierGadget<N: SNARK, F: Field> {
    type VerificationKeyGadget: AllocGadget<N::VerificationParameters, F>
        + AllocBytesGadget<Vec<u8>, F>
        + ToBytesGadget<F>;
    type ProofGadget: AllocGadget<N::Proof, F> + AllocBytesGadget<Vec<u8>, F>;

    fn check_verify<'a, CS: ConstraintSystem<F>, I: Iterator<Item = &'a T>, T: 'a + ToBitsBEGadget<F> + ?Sized>(
        cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        input: I,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError>;
}
