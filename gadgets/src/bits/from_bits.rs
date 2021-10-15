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

use crate::bits::Boolean;
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

pub trait FromBitsBEGadget<F: Field> {
    fn from_bits_be<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn from_bits_be_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

impl<F: Field> FromBitsBEGadget<F> for Boolean {
    fn from_bits_be<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn from_bits_be_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }
}

pub trait FromBitsLEGadget<F: Field> {
    fn from_bits_le<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    fn from_bits_le_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

impl<F: Field> FromBitsLEGadget<F> for Boolean {
    fn from_bits_le<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }

    fn from_bits_le_strict<CS: ConstraintSystem<F>>(bits: &[Boolean], _: CS) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }
}
