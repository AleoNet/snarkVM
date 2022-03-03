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

/// If condition is `true`, return `first`; else, select `second`.
pub trait CondSelectGadget<F: Field>
where
    Self: Sized,
{
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError>;

    fn cost() -> usize;
}

impl<F: Field, T: CondSelectGadget<F>> CondSelectGadget<F> for Vec<T> {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(first.len(), second.len());

        let mut res = Vec::<T>::with_capacity(first.len());
        for (i, (left, right)) in first.iter().zip(second.iter()).enumerate() {
            res.push(T::conditionally_select(cs.ns(|| format!("conditional_select_{}", i)), cond, left, right)?)
        }

        Ok(res)
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

/// Uses two bits to perform a lookup into a table
pub trait TwoBitLookupGadget<F: Field>
where
    Self: Sized,
{
    type TableConstant;
    fn two_bit_lookup<CS: ConstraintSystem<F>>(
        cs: CS,
        bits: &[Boolean],
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError>;

    fn cost() -> usize;
}

/// Uses three bits to perform a lookup into a table, where the last bit
/// performs negation
pub trait ThreeBitCondNegLookupGadget<F: Field>
where
    Self: Sized,
{
    type TableConstant;
    fn three_bit_cond_neg_lookup<CS: ConstraintSystem<F>>(
        cs: CS,
        bits: &[Boolean],
        b0b1: &Boolean,
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError>;

    fn cost() -> usize;
}
