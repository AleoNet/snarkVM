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

use crate::{integers::uint::*, traits::Cast, Boolean, Integer, UnsignedIntegerError};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::ConstraintSystem;

macro_rules! cast_uint_impl {
    ($($gadget: ident),*) => ($(
        impl<F: Field + PrimeField, Target: Integer> Cast<F, Target> for $gadget {
            type ErrorType = UnsignedIntegerError;
			type Output = Target;

            fn cast<CS: ConstraintSystem<F>>(
                &self,
                _cs: CS,
            ) -> Result<Self::Output, Self::ErrorType> {
                let bits = self.to_bits_le();

				let last_bit = bits[bits.len() - 1].clone();
				if Target::SIGNED && matches!(last_bit.get_value(), Some(true)) {
					// Wonder if error type should just be an Integer Error
					// Cause here it's technically a signed int overflow.
					return Err(UnsignedIntegerError::Overflow);
				}

				// If the target type is smaller than the current type
				if Target::SIZE <= Self::SIZE {
					// Since bits are le we check if the bits beyond target
					// size are set. If so we should error out because
					// the number is too big to fit into our target.
					if bits[Target::SIZE..].iter().any(|bit| matches!(bit.get_value(), Some(true))) {
						// Here it could a signed or unsigned overflow.
						Err(UnsignedIntegerError::Overflow)
					} else {
						Ok(Target::from_bits_le(&bits[0..Target::SIZE]))
					}
				} else {
					let mut bits = bits;

					for _ in Self::SIZE..Target::SIZE {
						bits.push(Boolean::Constant(false));
					}

					Ok(Target::from_bits_le(&bits[0..Target::SIZE]))
				}
            }
        }
    )*)
}

cast_uint_impl!(UInt8, UInt16, UInt32, UInt64, UInt128);
