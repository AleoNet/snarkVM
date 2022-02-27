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

use crate::bits::Boolean;
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

pub trait EvaluateLtGadget<F: Field> {
    fn less_than<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError>;
}

// implementing `EvaluateLtGadget` will implement `ComparatorGadget`
pub trait ComparatorGadget<F: Field>
where
    Self: EvaluateLtGadget<F>,
{
    fn greater_than<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        other.less_than(cs, self)
    }

    fn less_than_or_equal<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        let is_gt = self.greater_than(cs, other)?;
        Ok(is_gt.not())
    }

    fn greater_than_or_equal<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        other.less_than_or_equal(cs, self)
    }
}
