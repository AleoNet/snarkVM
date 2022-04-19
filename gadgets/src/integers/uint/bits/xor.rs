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

use crate::{integers::uint::*, traits::bits::Xor};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

macro_rules! uint_xor_impl {
    ($($gadget: ident),*) => ($(
        impl<F: PrimeField> Xor<F> for $gadget {
            fn xor<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
                let new_value = match (self.value, other.value) {
                    (Some(a), Some(b)) => Some(a ^ b),
                    _ => None,
                };

                let bits = self
                    .bits
                    .iter()
                    .zip(other.bits.iter())
                    .enumerate()
                    .map(|(i, (a, b))| a.xor(cs.ns(|| format!("xor of bit_gadget {}", i)), b))
                    .collect::<Result<_, _>>()?;

                Ok(Self {
                    bits,
                    negated: false,
                    value: new_value,
                })
            }
        }
    )*)
}

uint_xor_impl!(UInt8);
