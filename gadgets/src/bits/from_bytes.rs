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

use crate::{Boolean, UInt8};
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

pub trait FromBytesBEGadget<F: Field> {
    fn from_bytes_be<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    fn from_bytes_be_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

impl<F: Field> FromBytesBEGadget<F> for Boolean {
    fn from_bytes_be<CS: ConstraintSystem<F>>(bytes: &[UInt8], _: CS) -> Result<Boolean, SynthesisError> {
        if bytes.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bytes.get(0).ok_or_else(|| SynthesisError::Unsatisfiable)?;

        bytes.bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn from_bytes_be_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], _: CS) -> Result<Boolean, SynthesisError> {
        if bytes.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bytes.get(0).ok_or_else(|| SynthesisError::Unsatisfiable)?;

        bytes.bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }
}

pub trait FromBytesLEGadget<F: Field> {
    fn from_bytes_le<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    fn from_bytes_le_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

impl<F: Field> FromBytesLEGadget<F> for Boolean {
    fn from_bytes_le<CS: ConstraintSystem<F>>(bytes: &[UInt8], _: CS) -> Result<Boolean, SynthesisError> {
        if bytes.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bytes.get(0).ok_or_else(|| SynthesisError::Unsatisfiable)?;

        bytes.bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn from_bytes_le_strict<CS: ConstraintSystem<F>>(bytes: &[UInt8], _: CS) -> Result<Boolean, SynthesisError> {
        if bytes.len() != 1 {
            return Err(SynthesisError::AssignmentMissing);
        }

        let bytes = bytes.get(0).ok_or_else(|| SynthesisError::Unsatisfiable)?;

        bytes.bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }
}
