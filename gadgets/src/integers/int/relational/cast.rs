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

use crate::{errors::SignedIntegerError, integers::int::*, traits::Cast, Boolean, Integer};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::ConstraintSystem;

macro_rules! cast_int_impl {
    ($($gadget: ident)*) => ($(
        impl<F: PrimeField, Target: Integer> Cast<F, Target> for $gadget {
            type ErrorType = SignedIntegerError;
			type Output = Target;

            fn cast<CS: ConstraintSystem<F>>(
                &self,
                _cs: CS,
            ) -> Result<Self::Output, Self::ErrorType> {
                let bits = self.to_bits_le();

				dbg!(&bits);

				let last_bit = bits[bits.len() - 1].clone();
				dbg!(&last_bit);
				dbg!(bits[Target::SIZE]);

				// If the target type is smaller than the current type
				if Target::SIZE <= Self::SIZE {
					if Target::SIGNED && matches!(last_bit, Boolean::Constant(false))  && matches!(bits[Target::SIZE], Boolean::Constant(false)) && bits[..Target::SIZE-1].contains(&Boolean::Constant(false)) {
						// Positive signed to signed bounds checks.
						// Positive number bound checks last bit is false.
						Err(SignedIntegerError::Overflow)
					} else if Target::SIGNED && matches!(last_bit, Boolean::Constant(true)) && matches!(bits[Target::SIZE], Boolean::Constant(false)) && bits[..Target::SIZE-1].contains(&Boolean::Constant(true)) {
						// Negative signed to signed bounds checks.
						// Negative number bound checks last bit is true.
						Err(SignedIntegerError::Overflow)
					} else if !Target::SIGNED && matches!(last_bit, Boolean::Constant(true)) {
						// Negative signed to unsigned.
						// Wonder if error type should just be an Integer Error
						// Cause here it's technically a unsigned int overflow.
						Err(SignedIntegerError::Overflow)
					} else if !Target::SIGNED && bits[Target::SIZE..].contains(&Boolean::Constant(true)) {
						// Postive signed to unsigned.
						Err(SignedIntegerError::Overflow)
					} else {
						Ok(Target::from_bits_le(&bits[0..Target::SIZE]))
					}
				} else {
					let mut bits = bits;

					for _ in Self::SIZE..Target::SIZE {
						bits.push(last_bit.clone());
					}

					Ok(Target::from_bits_le(&bits[0..Target::SIZE]))
				}
            }
        }
    )*)
}

cast_int_impl!(Int8 Int16 Int32 Int64 Int128);
