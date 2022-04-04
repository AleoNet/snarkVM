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
use snarkvm_r1cs::ConstraintSystem;

use crate::{errors::UnsignedIntegerError, integers::uint::*};

/// Returns subtraction of `self` - `other` in the constraint system.
pub trait Sub<F: Field, Rhs = Self>
where
    Self: std::marker::Sized,
{
    type ErrorType;

    fn sub<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, Self::ErrorType>;
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
        }
    )*)
}

sub_int_impl!(UInt8);
