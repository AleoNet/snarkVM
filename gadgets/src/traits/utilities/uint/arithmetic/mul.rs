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
    arithmetic::Mul,
    boolean::Boolean,
    num::Number,
    select::CondSelectGadget,
    uint::*,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

macro_rules! mul_uint_impl {
    ($name: ident, $_type: ty, $size: expr) => {
        /// Bitwise multiplication of two signed integer objects.
        impl Mul for $name {
            type ErrorType = SynthesisError;

            fn mul<F: PrimeField, CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self,
            ) -> Result<Self, Self::ErrorType> {
                // pseudocode:
                //
                // res = 0;
                // shifted_self = self;
                // for bit in other.bits {
                //   if bit {
                //     res += shifted_self;
                //   }
                //   shifted_self = shifted_self << 1;
                // }
                // return res

                let is_constant = Boolean::constant(Self::result_is_constant(&self, &other));
                let constant_result = Self::constant(0 as $_type);
                let allocated_result = Self::alloc(
                    &mut cs.ns(|| format!("allocated_0u{}", $size)),
                    || Ok(0 as $_type),
                )?;
                let zero_result = Self::conditionally_select(
                    &mut cs.ns(|| "constant_or_allocated"),
                    &is_constant,
                    &constant_result,
                    &allocated_result,
                )?;

                let mut left_shift = self.clone();

                let partial_products = other
                    .bits
                    .iter()
                    .enumerate()
                    .map(|(i, bit)| {
                        let current_left_shift = left_shift.clone();
                        left_shift = Self::addmany(&mut cs.ns(|| format!("shift_left_{}", i)), &[
                            left_shift.clone(),
                            left_shift.clone(),
                        ])
                        .unwrap();

                        Self::conditionally_select(
                            &mut cs.ns(|| format!("calculate_product_{}", i)),
                            &bit,
                            &current_left_shift,
                            &zero_result,
                        )
                        .unwrap()
                    })
                    .collect::<Vec<Self>>();

                Self::addmany(&mut cs.ns(|| format!("partial_products")), &partial_products)
            }
        }
    };
}

mul_uint_impl!(UInt8, u8, 8);
mul_uint_impl!(UInt16, u16, 16);
mul_uint_impl!(UInt32, u32, 32);
mul_uint_impl!(UInt64, u64, 64);
mul_uint_impl!(UInt128, u128, 128);
