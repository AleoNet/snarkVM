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

use crate::{bits::Boolean, integers::int::*, traits::utilities::bits::RippleCarryAdder};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

macro_rules! rca_impl {
    ($($gadget: ident)*) => ($(
        impl<F: Field + PrimeField> RippleCarryAdder<F> for $gadget {
            fn add_bits<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Vec<Boolean>, SynthesisError> {
                self.bits.add_bits(cs, &other.bits)
            }
        }
    )*)
}

rca_impl!(Int8 Int16 Int32 Int64 Int128);
