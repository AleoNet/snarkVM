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
    arithmetic::{Mul, Pow},
    boolean::Boolean,
    num::Number,
    select::CondSelectGadget,
    uint::*,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

macro_rules! pow_uint_impl {
    ($name: ident, $_type: ty, $size: expr) => {
        impl Pow for $name {
            type ErrorType = SynthesisError;

            fn pow<F: PrimeField, CS: ConstraintSystem<F>>(
                &self,
                mut cs: CS,
                other: &Self,
            ) -> Result<Self, Self::ErrorType> {
                // let mut res = Self::one();
                //
                // for i in BitIteratorBE::new(exp) {
                //     res.square_in_place();
                //
                //     if i {
                //         res *= self;
                //     }
                // }
                // res

                let is_constant = Boolean::constant(Self::result_is_constant(&self, &other));
                let constant_result = Self::constant(1 as $_type);
                let allocated_result = Self::alloc(
                    &mut cs.ns(|| format!("allocated_1u{}", $size)),
                    || Ok(1 as $_type),
                )?;
                let mut result = Self::conditionally_select(
                    &mut cs.ns(|| "constant_or_allocated"),
                    &is_constant,
                    &constant_result,
                    &allocated_result,
                )?;

                for (i, bit) in other.bits.iter().rev().enumerate() {
                    result = result.mul(cs.ns(|| format!("square_{}", i)), &result).unwrap();

                    let mul_by_self = result
                        .mul(cs.ns(|| format!("multiply_by_self_{}", i)), &self)
                        .unwrap();

                    result = Self::conditionally_select(
                        &mut cs.ns(|| format!("mul_by_self_or_result_{}", i)),
                        &bit,
                        &mul_by_self,
                        &result,
                    )?;
                }

                Ok(result)
            }
        }
    };
}

pow_uint_impl!(UInt8, u8, 8);
pow_uint_impl!(UInt16, u16, 16);
pow_uint_impl!(UInt32, u32, 32);
pow_uint_impl!(UInt64, u64, 64);

impl Pow for UInt128 {
    type ErrorType = SynthesisError;

    /// Bitwise multiplication of two `UInt128` objects.
    /// Reference: /snarkVM/models/src/curves/field.rs
    fn pow<F: PrimeField, CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        // let mut res = Self::one();
        //
        // let mut found_one = false;
        //
        // for i in BitIteratorBE::new(exp) {
        //     if !found_one {
        //         if i {
        //             found_one = true;
        //         } else {
        //             continue;
        //         }
        //     }
        //
        //     res.square_in_place();
        //
        //     if i {
        //         res *= self;
        //     }
        // }
        // res

        let is_constant = Boolean::constant(Self::result_is_constant(&self, &other));
        let constant_result = Self::constant(1u128);
        let allocated_result = Self::alloc(&mut cs.ns(|| "allocated_1u128"), || Ok(1u128))?;
        let mut result = Self::conditionally_select(
            &mut cs.ns(|| "constant_or_allocated"),
            &is_constant,
            &constant_result,
            &allocated_result,
        )?;

        for (i, bit) in other.bits.iter().rev().enumerate() {
            let found_one = Boolean::Constant(result.eq(&Self::constant(1u128)));
            let cond1 = Boolean::and(cs.ns(|| format!("found_one_{}", i)), &bit.not(), &found_one)?;
            let square = result.mul(cs.ns(|| format!("square_{}", i)), &result).unwrap();

            result = Self::conditionally_select(
                &mut cs.ns(|| format!("result_or_sqaure_{}", i)),
                &cond1,
                &result,
                &square,
            )?;

            let mul_by_self = result.mul(cs.ns(|| format!("multiply_by_self_{}", i)), &self).unwrap();

            result = Self::conditionally_select(
                &mut cs.ns(|| format!("mul_by_self_or_result_{}", i)),
                &bit,
                &mul_by_self,
                &result,
            )?;
        }

        Ok(result)
    }
}
