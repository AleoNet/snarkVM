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

use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::integers::uint::UInt8;

pub trait ToBytesGadget<F: Field> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError>;
}

impl<'a, F: Field, T: 'a + ToBytesGadget<F>> ToBytesGadget<F> for &'a T {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        (*self).to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<'a, F: Field, T: 'a + ToBytesGadget<F>> ToBytesGadget<F> for &'a [T] {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut vec = vec![];
        for (i, elem) in self.iter().enumerate() {
            vec.append(&mut elem.to_bytes(cs.ns(|| format!("to_bytes_{}", i)))?);
        }
        Ok(vec)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut vec = vec![];
        for (i, elem) in self.iter().enumerate() {
            vec.append(&mut elem.to_bytes_strict(cs.ns(|| format!("to_bytes_{}", i)))?);
        }
        Ok(vec)
    }
}

impl<F: Field, T: ToBytesGadget<F>> ToBytesGadget<F> for [T] {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut vec = vec![];
        for (i, elem) in self.iter().enumerate() {
            vec.append(&mut elem.to_bytes(cs.ns(|| format!("to_bytes_{}", i)))?);
        }
        Ok(vec)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut vec = vec![];
        for (i, elem) in self.iter().enumerate() {
            vec.append(&mut elem.to_bytes_strict(cs.ns(|| format!("to_bytes_{}", i)))?);
        }
        Ok(vec)
    }
}

impl<F: Field, T: ToBytesGadget<F>> ToBytesGadget<F> for Vec<T> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut vec = vec![];
        for (i, elem) in self.iter().enumerate() {
            vec.append(&mut elem.to_bytes(cs.ns(|| format!("to_bytes_{}", i)))?);
        }
        Ok(vec)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut vec = vec![];
        for (i, elem) in self.iter().enumerate() {
            vec.append(&mut elem.to_bytes_strict(cs.ns(|| format!("to_bytes_{}", i)))?);
        }
        Ok(vec)
    }
}
