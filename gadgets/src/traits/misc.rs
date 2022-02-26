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

use crate::Boolean;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

pub trait MergeGadget<F: PrimeField>: Clone {
    fn merge<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;
    fn merge_in_place<CS: ConstraintSystem<F>>(&mut self, cs: CS, other: &Self) -> Result<(), SynthesisError>;
    fn merge_many<CS: ConstraintSystem<F>>(mut cs: CS, elems: &[Self]) -> Result<Self, SynthesisError> {
        assert!(!elems.is_empty());

        let mut res = elems[0].clone();
        for (i, elem) in elems.iter().skip(1).enumerate() {
            res.merge_in_place(cs.ns(|| format!("merge_{}", i)), elem)?;
        }

        Ok(res)
    }
}

pub trait SumGadget<F: PrimeField>: Clone {
    fn zero<CS: ConstraintSystem<F>>(cs: CS) -> Result<Self, SynthesisError>;
    fn sum<CS: ConstraintSystem<F>>(cs: CS, elems: &[Self]) -> Result<Self, SynthesisError>;
}

pub trait ToMinimalBitsGadget<F: PrimeField>: Clone {
    fn to_minimal_bits<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError>;
}

impl<F: PrimeField, T: ToMinimalBitsGadget<F>> ToMinimalBitsGadget<F> for Vec<T> {
    fn to_minimal_bits<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut res_booleans = vec![];
        for (i, elem) in self.iter().enumerate() {
            res_booleans.extend(elem.to_minimal_bits(cs.ns(|| i.to_string()))?);
        }

        Ok(res_booleans)
    }
}
