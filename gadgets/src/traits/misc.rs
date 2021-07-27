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

use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

pub trait MergeGadget<F: PrimeField>: Clone {
    fn merge<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;
    fn merge_in_place<CS: ConstraintSystem<F>>(&mut self, cs: CS, other: &Self) -> Result<(), SynthesisError>;
    fn merge_many<CS: ConstraintSystem<F>>(mut cs: CS, elems: &[Self]) -> Result<Self, SynthesisError> {
        assert!(elems.len() >= 1);

        let mut res = elems[0].clone();
        for (i, elem) in elems.iter().skip(1).enumerate() {
            res.merge_in_place(cs.ns(|| format!("merge_{}", i)), elem)?;
        }

        Ok(res)
    }
}
