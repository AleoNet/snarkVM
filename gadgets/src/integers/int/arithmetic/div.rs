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
    errors::{SignedIntegerError, UnsignedIntegerError},
    integers::int::*,
    traits::{
        eq::{EqGadget, EvaluateEqGadget},
        integers::{Div, Integer, Neg},
        select::CondSelectGadget,
    },
};

macro_rules! div_int_impl {
    ($($gadget:ident),*) => ($(
        impl<F: PrimeField> Div<F> for $gadget {
            type ErrorType = SignedIntegerError;

            fn div<CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self
            ) -> Result<Self, Self::ErrorType> {
                // N / D pseudocode:
                //
                // if D = 0 then error(DivisionByZeroException) end
                //
                // positive = msb(N) == msb(D) -- if msb's equal, return positive result
                //
                // Q := 0                  -- Initialize quotient and remainder to zero
                // R := 0
                //
                // for i := n − 1 .. 0 do  -- Where n is number of bits in N
                //   R := R << 1           -- Left-shift R by 1 bit
                //   R(0) := N(i)          -- Set the least-significant bit of R equal to bit i of the numerator
                //   if R ≥ D then
                //     R := R − D
                //     Q(i) := 1
                //   end
                // end
                //
                // if positive then           -- positive result
                //    Q
                // else
                //    !Q                      -- negative result

                // Check if other is already known to be zero.
                if let Some(value) = other.value {
                    if value == 0 as <$gadget as Integer>::IntegerType {
                        return Err(SignedIntegerError::DivisionByZero.into());
                    }
                }

                // If `self` and `other` are both constants, return the constant result instead of generating constraints.
                if self.is_constant() && other.is_constant() {
                    return Ok(Self::constant(self.value.unwrap().wrapping_div(other.value.unwrap())));
                }

                // If `self` = MIN and `other` = -1, reject as this causes an overflow.
                if self.value.is_some() && other.value.is_some() {
                    if self.value.unwrap() == <$gadget as Integer>::IntegerType::MIN && other.value.unwrap() == -1 {
                        return Err(SignedIntegerError::Overflow.into());
                    }
                }
                let self_is_min = self.evaluate_equal(cs.ns(||"is_self_min"), &Self::constant(<$gadget as Integer>::IntegerType::MIN))?;
                let other_is_minus_one = other.evaluate_equal(cs.ns(||"is_other_minus_one"), &Self::constant(-1 as <$gadget as Integer>::IntegerType))?;
                Boolean::and(cs.ns(||"is_result_overflowing"), &self_is_min, &other_is_minus_one)?.enforce_equal(cs.ns(||"result_cannot_be_overflowing"), &Boolean::constant(false))?;

                let is_a_negative = self.bits.last().unwrap();
                let is_b_negative = other.bits.last().unwrap();
                let positive_result = is_a_negative.evaluate_equal(cs.ns(|| "compare_msb"), &is_b_negative)?;

                // Get the absolute value of each number.
                let a_absolute : <$gadget as Integer>::UnsignedGadget = {
                    let negated_bits = self.bits.neg(cs.ns(||"neg_self_bits"))?;

                    let mut absolute_value_bits = Vec::with_capacity(self.bits.len());
                    for i in 0..self.bits.len() {
                        absolute_value_bits.push(Boolean::conditionally_select(
                            cs.ns(|| format!("select_the_self_absolute_value_bit_{}", i)),
                            &is_a_negative,
                            &negated_bits[i],
                            &self.bits[i],
                        )?);
                    }

                    <$gadget as Integer>::UnsignedGadget::from_bits_le(&absolute_value_bits, cs.ns(||"a_absolute_value_bits"))?
                };
                let b_absolute : <$gadget as Integer>::UnsignedGadget = {
                    let negated_bits = other.bits.neg(cs.ns(||"neg_other_bits"))?;

                    let mut absolute_value_bits = Vec::with_capacity(self.bits.len());
                    for i in 0..self.bits.len() {
                        absolute_value_bits.push(Boolean::conditionally_select(
                            cs.ns(|| format!("select_the_other_absolute_value_bit_{}", i)),
                            &is_b_negative,
                            &negated_bits[i],
                            &other.bits[i],
                        )?);
                    }

                    <$gadget as Integer>::UnsignedGadget::from_bits_le(&absolute_value_bits, cs.ns(||"b_absolute_value_bits"))?
                };

                let quotient = a_absolute.div(cs.ns(||"div_absolute_value"), &b_absolute).map_err(
                    |err|
                    match err {
                        UnsignedIntegerError::Overflow => SignedIntegerError::Overflow,
                        UnsignedIntegerError::DivisionByZero => SignedIntegerError::DivisionByZero,
                        UnsignedIntegerError::SynthesisError(e) => SignedIntegerError::SynthesisError(e),
                    }
                )?;

                let negated_quotient_bits = quotient.bits.neg(cs.ns(||"neg_quotient_bits"))?;

                let mut result_bits = Vec::<Boolean>::with_capacity(quotient.bits.len());
                for i in 0..quotient.bits.len() {
                    result_bits.push(Boolean::conditionally_select(
                        cs.ns(|| format!("select_final_bits_{}", i)),
                        &positive_result,
                        &quotient.bits[i],
                        &negated_quotient_bits[i],
                    )?);
                }

                let quotient = Self::from_bits_le(&result_bits, cs)?;
                Ok(quotient)
            }
        }
    )*)
}

div_int_impl!(Int8, Int16, Int32, Int64, Int128);
