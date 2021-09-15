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
    integer::Integer,
    integers::{int::*, uint::UInt8},
    ToBytesGadget,
};
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

macro_rules! to_bytes_impl {
    ($gadget: ident, $size: expr) => {
        impl<F: Field> ToBytesGadget<F> for $gadget {
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

to_bytes_impl!(Int8, 8);
to_bytes_impl!(Int16, 16);
to_bytes_impl!(Int32, 32);
to_bytes_impl!(Int64, 64);
to_bytes_impl!(Int128, 128);

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
