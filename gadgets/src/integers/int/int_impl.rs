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

use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::ToBytes;

use crate::{
    bits::{
        Boolean,
        FromBitsBEGadget,
        FromBitsLEGadget,
        FromBytesBEGadget,
        FromBytesLEGadget,
        ToBitsBEGadget,
        ToBitsLEGadget,
        ToBytesBEGadget,
        ToBytesLEGadget,
    },
    integers::uint::{UInt128, UInt16, UInt32, UInt64, UInt8},
    traits::integers::Integer,
};

use std::fmt::Debug;

/// Implements the base struct for a signed integer gadget
macro_rules! int_impl {
    ($name: ident, $type_: ty, $uname_: ty, $utype_: ty, $size: expr) => {
        #[derive(Clone, Debug)]
        pub struct $name {
            pub bits: Vec<Boolean>,
            pub value: Option<$type_>,
        }

        impl Integer for $name {
            type IntegerType = $type_;
            type UnsignedGadget = $uname_;
            type UnsignedIntegerType = $utype_;

            const SIZE: usize = $size;

            fn constant(value: $type_) -> Self {
                let mut bits = Vec::with_capacity($size);

                for i in 0..$size {
                    // shift value by i
                    let mask = 1 << i as $type_;
                    let result = value & mask;

                    // If last bit is one, push one.
                    if result == mask {
                        bits.push(Boolean::constant(true))
                    } else {
                        bits.push(Boolean::constant(false))
                    }
                }

                Self {
                    bits,
                    value: Some(value),
                }
            }

            fn one() -> Self {
                Self::constant(1 as $type_)
            }

            fn zero() -> Self {
                Self::constant(0 as $type_)
            }

            fn new(bits: Vec<Boolean>, value: Option<Self::IntegerType>) -> Self {
                Self { bits, value }
            }

            fn is_constant(&self) -> bool {
                // If any bits of self are allocated bits, return false
                self.bits.iter().all(|bit| matches!(bit, Boolean::Constant(_)))
            }

            fn get_value(&self) -> Option<String> {
                self.value.map(|num| num.to_string())
            }
        }

        to_bits_int_impl!($name);
        to_bytes_int_impl!($name, $size);

        from_bits_int_impl!($name, $type_, $utype_, $size);
        from_bytes_int_impl!($name, $type_, { $size / UInt8::SIZE });
    };
}

int_impl!(Int8, i8, UInt8, u8, 8);
int_impl!(Int16, i16, UInt16, u16, 16);
int_impl!(Int32, i32, UInt32, u32, 32);
int_impl!(Int64, i64, UInt64, u64, 64);
int_impl!(Int128, i128, UInt128, u128, 128);
