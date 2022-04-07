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

use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::Boolean,
    integers::uint::*,
    traits::{
        eq::{ConditionalEqGadget, EqGadget, EvaluateEqGadget},
        integers::Integer,
    },
};

macro_rules! eq_gadget_impl {
    ($($gadget: ident)*) => ($(
        impl<F: PrimeField> EvaluateEqGadget<F> for $gadget {
            fn evaluate_equal<CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self
            ) -> Result<Boolean, SynthesisError> {
                let mut result = Boolean::constant(true);
                for (i, (a, b)) in self.bits.iter().zip(&other.bits).enumerate() {
                    let equal = a.evaluate_equal(
                        &mut cs.ns(|| format!("{} evaluate equality for {}-th bit", <$gadget as Integer>::SIZE, i)),
                        b,
                    )?;

                    result = Boolean::and(
                        &mut cs.ns(|| format!("{} and result for {}-th bit", <$gadget as Integer>::SIZE, i)),
                        &equal,
                        &result,
                    )?;
                }

                Ok(result)
            }
        }

        impl PartialEq for $gadget {
            fn eq(&self, other: &Self) -> bool {
                !self.value.is_none() && self.value == other.value
            }
        }

        impl Eq for $gadget {}
    )*)
}

macro_rules! cond_eq_int_impl {
    ($($gadget: ident)*) => ($(

        impl<F: Field> EqGadget<F> for $gadget {
            fn is_eq<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
                self.bits.is_eq(cs.ns(|| "bits_is_eq"), &other.bits)
            }
        }

        impl<F: Field> ConditionalEqGadget<F> for $gadget {
            fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self,
                condition: &Boolean,
            ) -> Result<(), SynthesisError> {
                for (i, (a, b)) in self.bits.iter().zip(&other.bits).enumerate() {
                    a.conditional_enforce_equal(
                        &mut cs.ns(|| format!("{} equality check for the {}-th bit", <$gadget as Integer>::SIZE, i)),
                        b,
                        condition,
                    )?;
                }

                Ok(())
            }

            fn cost() -> usize {
                <$gadget as Integer>::SIZE * <Boolean as ConditionalEqGadget<F>>::cost()
            }
        }
    )*)
}

eq_gadget_impl!(UInt8);

cond_eq_int_impl!(UInt8);
