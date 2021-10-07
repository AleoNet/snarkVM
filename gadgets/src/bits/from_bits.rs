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
use snarkvm_r1cs::errors::SynthesisError;

pub trait FromBitsLEGadget {
    fn from_bits_le(bits: &[Boolean]) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    fn from_bits_le_strict(bits: &[Boolean]) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

impl FromBitsLEGadget for Boolean {
    fn from_bits_le(bits: &[Boolean]) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::Unsatisfiable);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }

    fn from_bits_le_strict(bits: &[Boolean]) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::Unsatisfiable);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }
}

pub trait FromBitsBEGadget {
    fn from_bits_be(bits: &[Boolean]) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn from_bits_be_strict(bits: &[Boolean]) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

impl FromBitsBEGadget for Boolean {
    fn from_bits_be(bits: &[Boolean]) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::Unsatisfiable);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn from_bits_be_strict(bits: &[Boolean]) -> Result<Boolean, SynthesisError> {
        if bits.len() != 1 {
            return Err(SynthesisError::Unsatisfiable);
        }

        bits.get(0).copied().ok_or_else(|| SynthesisError::Unsatisfiable)
    }
}
