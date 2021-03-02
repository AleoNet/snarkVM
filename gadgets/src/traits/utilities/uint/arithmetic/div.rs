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

use crate::utilities::{
    alloc::AllocGadget,
    arithmetic::Div,
    boolean::{AllocatedBit, Boolean},
    num::Number,
    select::CondSelectGadget,
    uint::*,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

macro_rules! div_uint_impl {
    ($name: ident, $_type: ty, $size: expr) => {
        impl Div for $name {
            type ErrorType = SynthesisError;

            fn div<F: PrimeField, CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self,
            ) -> Result<Self, Self::ErrorType> {
                // pseudocode:
                //
                // if D = 0 then error(DivisionByZeroException) end
                // Q := 0                  -- Initialize quotient and remainder to zero
                // R := 0
                // for i := n − 1 .. 0 do  -- Where n is number of bits in N
                //   R := R << 1           -- Left-shift R by 1 bit
                //   R(0) := N(i)          -- Set the least-significant bit of R equal to bit i of the numerator
                //   if R ≥ D then
                //     R := R − D
                //     Q(i) := 1
                //   end
                // end

                if other.eq(&Self::constant(0 as $_type)) {
                    return Err(SynthesisError::DivisionByZero);
                }

                let is_constant = Boolean::constant(Self::result_is_constant(&self, &other));

                let allocated_true = Boolean::from(AllocatedBit::alloc(&mut cs.ns(|| "true"), || Ok(true)).unwrap());
                let true_bit = Boolean::conditionally_select(
                    &mut cs.ns(|| "constant_or_allocated_true"),
                    &is_constant,
                    &Boolean::constant(true),
                    &allocated_true,
                )?;

                let allocated_one = Self::alloc(&mut cs.ns(|| "one"), || Ok(1 as $_type))?;
                let one = Self::conditionally_select(
                    &mut cs.ns(|| format!("constant_or_allocated_1u{}", $size)),
                    &is_constant,
                    &Self::constant(1 as $_type),
                    &allocated_one,
                )?;

                let allocated_zero = Self::alloc(&mut cs.ns(|| "zero"), || Ok(0 as $_type))?;
                let zero = Self::conditionally_select(
                    &mut cs.ns(|| format!("constant_or_allocated_0u{}", $size)),
                    &is_constant,
                    &Self::constant(0 as $_type),
                    &allocated_zero,
                )?;

                let self_is_zero = Boolean::Constant(self.eq(&Self::constant(0 as $_type)));
                let mut quotient = zero.clone();
                let mut remainder = zero.clone();

                for (i, bit) in self.bits.iter().rev().enumerate() {
                    // Left shift remainder by 1
                    remainder = Self::addmany(&mut cs.ns(|| format!("shift_left_{}", i)), &[
                        remainder.clone(),
                        remainder.clone(),
                    ])?;

                    // Set the least-significant bit of remainder to bit i of the numerator
                    let bit_is_true = Boolean::constant(bit.eq(&Boolean::constant(true)));
                    let new_remainder = Self::addmany(&mut cs.ns(|| format!("set_remainder_bit_{}", i)), &[
                        remainder.clone(),
                        one.clone(),
                    ])?;

                    remainder = Self::conditionally_select(
                        &mut cs.ns(|| format!("increment_or_remainder_{}", i)),
                        &bit_is_true,
                        &new_remainder,
                        &remainder,
                    )?;

                    // Greater than or equal to:
                    //   R >= D
                    //   (R == D) || (R > D)
                    //   (R == D) || ((R !=D) && ((R - D) != 0))
                    //
                    //  (R > D)                     checks subtraction overflow before evaluation
                    //  (R != D) && ((R - D) != 0)  instead evaluate subtraction and check for overflow after

                    let no_remainder = Boolean::constant(remainder.eq(&other));
                    let subtraction = remainder.sub_unsafe(&mut cs.ns(|| format!("subtract_divisor_{}", i)), &other)?;
                    let sub_is_zero = Boolean::constant(subtraction.eq(&Self::constant(0 as $_type)));
                    let cond1 = Boolean::and(
                        &mut cs.ns(|| format!("cond_1_{}", i)),
                        &no_remainder.not(),
                        &sub_is_zero.not(),
                    )?;
                    let cond2 = Boolean::or(&mut cs.ns(|| format!("cond_2_{}", i)), &no_remainder, &cond1)?;

                    remainder = Self::conditionally_select(
                        &mut cs.ns(|| format!("subtract_or_same_{}", i)),
                        &cond2,
                        &subtraction,
                        &remainder,
                    )?;

                    let index = $size - 1 - i as usize;
                    let bit_value = (1 as $_type) << (index as $_type);
                    let mut new_quotient = quotient.clone();
                    new_quotient.bits[index] = true_bit;
                    new_quotient.value = Some(new_quotient.value.unwrap() + bit_value);

                    quotient = Self::conditionally_select(
                        &mut cs.ns(|| format!("set_bit_or_same_{}", i)),
                        &cond2,
                        &new_quotient,
                        &quotient,
                    )?;
                }
                Self::conditionally_select(&mut cs.ns(|| "self_or_quotient"), &self_is_zero, self, &quotient)
            }
        }
    };
}

div_uint_impl!(UInt8, u8, 8);
div_uint_impl!(UInt16, u16, 16);
div_uint_impl!(UInt32, u32, 32);
div_uint_impl!(UInt64, u64, 64);
div_uint_impl!(UInt128, u128, 128);
