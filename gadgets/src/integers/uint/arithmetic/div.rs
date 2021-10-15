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
use snarkvm_r1cs::ConstraintSystem;

use crate::{
    bits::{boolean::Boolean, FromBitsLEGadget},
    errors::UnsignedIntegerError,
    integers::uint::*,
    traits::{
        alloc::AllocGadget,
        bits::EvaluateLtGadget,
        eq::{EqGadget, EvaluateEqGadget},
        integers::{Add, Div, Integer},
        select::CondSelectGadget,
    },
};

/// Perform long division of two `UInt` objects.
/// Reference: https://en.wikipedia.org/wiki/Division_algorithm
macro_rules! div_int_impl {
    ($($gadget:ident),*) => ($(
        impl<F: PrimeField> Div<F> for $gadget {
            type ErrorType = UnsignedIntegerError;

            fn div<CS: ConstraintSystem<F>>(
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

                // Enforce D != 0
                if !other.is_constant() {
                    other.evaluate_equal(cs.ns(||"is_divisor_zero"), &Self::constant(0 as <$gadget as Integer>::IntegerType))?.enforce_equal(cs.ns(||"divisor_is_not_zero"), &Boolean::constant(false))?;
                }
                if let Some(value) = other.value {
                    if value == 0 as <$gadget as Integer>::IntegerType {
                        return Err(UnsignedIntegerError::DivisionByZero.into());
                    }
                }

                // If `self` and `other` are both constants, return the constant result instead of generating constraints.
                if self.is_constant() && other.is_constant() {
                    return Ok(Self::constant(self.value.unwrap().wrapping_div(other.value.unwrap())));
                }

                // Initialize some constants
                let one = Self::constant(1 as <$gadget as Integer>::IntegerType);
                let zero = Self::constant(0 as <$gadget as Integer>::IntegerType);

                // Q := 0
                let mut quotient_bits = Vec::new();

                // R := 0
                let mut remainder = zero.clone();

                // for i := n - 1 .. 0 do
                for (i, bit) in self.bits.iter().rev().enumerate() {
                    // R := R << 1
                    remainder = remainder.add(cs.ns(|| format!("R_double_{}", i)), &remainder)?;

                    // R(0) := N(i)
                    let remainder_plus_one = remainder.add(cs.ns(|| format!("set_remainder_bit_{}", i)), &one)?;
                    remainder = Self::conditionally_select(
                        &mut cs.ns(|| format!("increment_or_remainder_{}", i)),
                        &bit,
                        &remainder_plus_one,
                        &remainder,
                    )?;

                    // if R ≥ D
                    let r_larger_or_equal_to_d = remainder.less_than(cs.ns(|| format!("check_if_R_greater_than_D_{}", i)), &other)?.not();

                    // compute R - D
                    let r_sub_d = {
                        let result = Self::alloc(cs.ns(||format!("r_sub_d_result_{}", i)), || {
                            let remainder_value = remainder.value.unwrap();
                            let divisor_value = other.value.unwrap();

                            if remainder_value < divisor_value {
                                Ok(0 as <$gadget as Integer>::IntegerType)
                            } else{
                                Ok(remainder_value - divisor_value)
                            }
                        })?;
                        let result_plus_d = result.add(cs.ns(|| format!("r_sub_d_add_d_{}", i)), &other)?;
                        let result_plus_d_sub_r = result_plus_d.sub(cs.ns(|| format!("r_sub_d_add_d_sub_r_{}", i)), &remainder)?;
                        let should_be_zero = Self::conditionally_select(
                            cs.ns(|| format!("select_result_plus_d_sub_r_or_zero_{}", i)),
                            &r_larger_or_equal_to_d,
                            &result_plus_d_sub_r,
                            &zero,
                        )?;
                        should_be_zero.enforce_equal(cs.ns(|| format!("should_be_zero_{}", i)), &zero)?;

                        result
                    };

                    remainder = Self::conditionally_select(
                        &mut cs.ns(|| format!("subtract_or_same_{}", i)),
                        &r_larger_or_equal_to_d,
                        &r_sub_d,
                        &remainder,
                    )?;

                    // Q(i) := 1
                    quotient_bits.push(r_larger_or_equal_to_d);
                }

                quotient_bits.reverse();

                let quotient = Self::from_bits_le(&quotient_bits, cs)?;
                Ok(quotient)
            }
        }
    )*)
}

div_int_impl!(UInt8, UInt16, UInt32, UInt64, UInt128);
