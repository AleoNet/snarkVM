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

use crate::{bits::Boolean, integers::uint::UInt8, traits::integers::Integer};
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

pub trait ToBitsBEGadget<F: Field> {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError>;
}

impl<F: Field> ToBitsBEGadget<F> for Boolean {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }
}

impl<F: Field> ToBitsBEGadget<F> for [Boolean] {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }
}

impl<F: Field> ToBitsBEGadget<F> for Vec<Boolean> {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }
}

impl<F: Field> ToBitsBEGadget<F> for [UInt8] {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut result = Vec::with_capacity(&self.len() * 8);
        for byte in self {
            result.extend_from_slice(&byte.to_bits_be());
        }
        Ok(result)
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_be(cs)
    }
}

pub trait ToBitsLEGadget<F: Field> {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError>;
}

impl<F: Field> ToBitsLEGadget<F> for Boolean {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, _: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }
}

impl<F: Field> ToBitsLEGadget<F> for [Boolean] {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }
}

impl<F: Field> ToBitsLEGadget<F> for Vec<Boolean> {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }
}

impl<F: Field> ToBitsLEGadget<F> for [UInt8] {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut result = Vec::with_capacity(&self.len() * 8);
        for byte in self {
            result.extend_from_slice(&byte.to_bits_le());
        }
        Ok(result)
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_le(cs)
    }
}
