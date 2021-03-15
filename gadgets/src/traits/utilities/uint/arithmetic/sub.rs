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

use crate::{
    errors::UnsignedIntegerError,
    utilities::{alloc::AllocGadget, boolean::AllocatedBit, uint::*, Field, SynthesisError},
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{Assignment, ConstraintSystem, LinearCombination};

/// Returns subtraction of `self` - `other` in the constraint system.
pub trait Sub<F: Field, Rhs = Self>
where
    Self: std::marker::Sized,
{
    type ErrorType;

    fn sub<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, Self::ErrorType>;

    fn sub_unsafe<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, Self::ErrorType>;
}

macro_rules! sub_int_impl {
    ($($gadget:ident),*) => ($(
        impl<F: PrimeField> Sub<F> for $gadget {
            type ErrorType = UnsignedIntegerError;

            fn sub<CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self,
            ) -> Result<Self, Self::ErrorType> {
                // pseudocode:
                //
                // a - b
                // a + (-b)

                Self::addmany(&mut cs.ns(|| "add_not"), &[self.clone(), other.negate()]).map_err(|e| e.into())
            }

            /// Used for division. Evaluates a - b, and when a - b < 0, returns 0.
            fn sub_unsafe<CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self,
            ) -> Result<Self, Self::ErrorType> {
                match (self.value, other.value) {
                    (Some(val1), Some(val2)) => {
                        // Check for overflow
                        if val1 < val2 {
                            // Instead of erroring, return 0

                            if Self::result_is_constant(&self, &other) {
                                // Return constant 0
                                Ok(Self::constant(0 as <$gadget as UInt>::IntegerType))
                            } else {
                                // Return allocated 0
                                let result_value = Some(0u128);
                                let modular_value = result_value.map(|v| v as <$gadget as UInt>::IntegerType);

                                // Storage area for the resulting bits
                                let mut result_bits = Vec::with_capacity(<$gadget as UInt>::SIZE);

                                // This is a linear combination that we will enforce to be "zero"
                                let mut lc = LinearCombination::zero();

                                // Allocate each bit_gadget of the result
                                let mut coeff = F::one();
                                for i in 0..<$gadget as UInt>::SIZE {
                                    // Allocate the bit_gadget
                                    let b = AllocatedBit::alloc(cs.ns(|| format!("result bit_gadget {}", i)), || {
                                        result_value.map(|v| (v >> i) & 1 == 1).get()
                                    })?;

                                    // Subtract this bit_gadget from the linear combination to ensure the sums
                                    // balance out
                                    lc = lc - (coeff, b.get_variable());

                                    result_bits.push(b.into());

                                    coeff.double_in_place();
                                }

                                // Enforce that the linear combination equals zero
                                cs.enforce(|| "unsafe subtraction", |lc| lc, |lc| lc, |_| lc);

                                Ok(Self {
                                    bits: result_bits,
                                    negated: false,
                                    value: modular_value,
                                })
                            }
                        } else {
                            // Perform subtraction
                            self.sub(&mut cs.ns(|| ""), &other)
                        }
                    }
                    (_, _) => {
                        // If either of our operands have unknown value, we won't
                        // know the value of the result
                        Err(SynthesisError::AssignmentMissing.into())
                    }
                }
            }
        }
    )*)
}

sub_int_impl!(UInt8, UInt16, UInt32, UInt64, UInt128);
