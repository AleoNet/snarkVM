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
    bits::Boolean,
    integers::uint::{UInt128, UInt16, UInt32, UInt64, UInt8},
    traits::integers::Integer,
    ToBytesGadget,
};
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

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

            fn to_bits_le(&self) -> Vec<Boolean> {
                self.bits.clone()
            }

            fn to_bits_be(&self) -> Vec<Boolean> {
                debug_assert_eq!(self.bits.len(), $size);
                let mut res = self.bits.clone();
                res.reverse();
                res
            }

            fn from_bits_le(bits: &[Boolean]) -> Self {
                assert_eq!(bits.len(), $size);

                let bits = bits.to_vec();

                let mut value = Some(0 as $utype_);
                for b in bits.iter().rev() {
                    value.as_mut().map(|v| *v <<= 1);

                    match *b {
                        Boolean::Constant(b) => {
                            if b {
                                value.as_mut().map(|v| *v |= 1);
                            }
                        }
                        Boolean::Is(ref b) => match b.get_value() {
                            Some(true) => {
                                value.as_mut().map(|v| *v |= 1);
                            }
                            Some(false) => {}
                            None => value = None,
                        },
                        Boolean::Not(ref b) => match b.get_value() {
                            Some(false) => {
                                value.as_mut().map(|v| *v |= 1);
                            }
                            Some(true) => {}
                            None => value = None,
                        },
                    }
                }

                Self {
                    value: value.map(|x| x as $type_),
                    bits,
                }
            }

            fn get_value(&self) -> Option<String> {
                self.value.map(|num| num.to_string())
            }
        }

        impl<F: Field> ToBytesGadget<F> for $name {
            #[inline]
            fn to_bytes<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                let bits = self.to_bits_le();
                debug_assert_eq!($size, bits.len());

                let value_bytes = self.value.map_or(vec![None; $size / 8], |value| {
                    value.to_le_bytes().iter().map(|byte| Some(*byte)).collect()
                });

                Ok(bits
                    .chunks(8)
                    .into_iter()
                    .zip(value_bytes)
                    .map(|(chunk8, value)| UInt8 {
                        bits: chunk8.to_vec(),
                        negated: false,
                        value,
                    })
                    .collect())
            }

            fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
                self.to_bytes(cs)
            }
        }
    };
}

int_impl!(Int8, i8, UInt8, u8, 8);
int_impl!(Int16, i16, UInt16, u16, 16);
int_impl!(Int32, i32, UInt32, u32, 32);
int_impl!(Int64, i64, UInt64, u64, 64);
int_impl!(Int128, i128, UInt128, u128, 128);

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

    use num_traits::PrimInt;
    use rand::{thread_rng, Rng};

    const ITERATIONS: usize = 100_000;

    #[test]
    fn test_int_to_bytes() {
        fn int_to_bytes_test<F: Field, I: PrimInt, Int: Integer<IntegerType = I> + ToBytesGadget<F>>(
            expected: I,
            expected_bytes: &[u8],
        ) {
            let mut cs = TestConstraintSystem::<F>::new();

            let candidate = Int::constant(expected);
            let candidate_bytes = candidate.to_bytes(cs.ns(|| "to_bytes")).unwrap();
            assert_eq!(expected_bytes.len(), candidate_bytes.len());

            for (expected_byte, candidate_byte) in expected_bytes.iter().zip(candidate_bytes) {
                println!("{} == {}", expected_byte, candidate_byte.value.unwrap());
                assert_eq!(*expected_byte, candidate_byte.value.unwrap());
            }
        }

        for _ in 0..ITERATIONS {
            // 8-bit signed integer
            let expected: i8 = thread_rng().gen();
            int_to_bytes_test::<Fr, i8, Int8>(expected, &expected.to_le_bytes());

            // 16-bit signed integer
            let expected: i16 = thread_rng().gen();
            int_to_bytes_test::<Fr, i16, Int16>(expected, &expected.to_le_bytes());

            // 32-bit signed integer
            let expected: i32 = thread_rng().gen();
            int_to_bytes_test::<Fr, i32, Int32>(expected, &expected.to_le_bytes());

            // 64-bit signed integer
            let expected: i64 = thread_rng().gen();
            int_to_bytes_test::<Fr, i64, Int64>(expected, &expected.to_le_bytes());

            // 128-bit signed integer
            let expected: i128 = thread_rng().gen();
            int_to_bytes_test::<Fr, i128, Int128>(expected, &expected.to_le_bytes());
        }
    }
}
