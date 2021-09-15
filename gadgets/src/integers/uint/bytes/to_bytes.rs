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

use crate::{integer::Integer, integers::uint::*, ToBytesGadget};
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

to_bytes_impl!(UInt8, 8);
to_bytes_impl!(UInt16, 16);
to_bytes_impl!(UInt32, 32);
to_bytes_impl!(UInt64, 64);
to_bytes_impl!(UInt128, 128);

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

    use num_traits::PrimInt;
    use rand::{thread_rng, Rng};

    const ITERATIONS: usize = 100_000;

    #[test]
    fn test_uint_to_bytes() {
        fn uint_to_bytes_test<F: Field, U: PrimInt, UInt: Integer<IntegerType = U> + ToBytesGadget<F>>(
            expected: U,
            expected_bytes: &[u8],
        ) {
            let mut cs = TestConstraintSystem::<F>::new();

            let candidate = UInt::constant(expected);
            let candidate_bytes = candidate.to_bytes(cs.ns(|| "to_bytes")).unwrap();
            assert_eq!(expected_bytes.len(), candidate_bytes.len());

            for (expected_byte, candidate_byte) in expected_bytes.iter().zip(candidate_bytes) {
                println!("{} == {}", expected_byte, candidate_byte.value.unwrap());
                assert_eq!(*expected_byte, candidate_byte.value.unwrap());
            }
        }

        for _ in 0..ITERATIONS {
            // 8-bit unsigned integer
            let expected: u8 = thread_rng().gen();
            uint_to_bytes_test::<Fr, u8, UInt8>(expected, &expected.to_le_bytes());

            // 16-bit unsigned integer
            let expected: u16 = thread_rng().gen();
            uint_to_bytes_test::<Fr, u16, UInt16>(expected, &expected.to_le_bytes());

            // 32-bit unsigned integer
            let expected: u32 = thread_rng().gen();
            uint_to_bytes_test::<Fr, u32, UInt32>(expected, &expected.to_le_bytes());

            // 64-bit unsigned integer
            let expected: u64 = thread_rng().gen();
            uint_to_bytes_test::<Fr, u64, UInt64>(expected, &expected.to_le_bytes());

            // 128-bit unsigned integer
            let expected: u128 = thread_rng().gen();
            uint_to_bytes_test::<Fr, u128, UInt128>(expected, &expected.to_le_bytes());
        }
    }
}
