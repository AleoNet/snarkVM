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

use super::*;

// TODO: Resolve usize vs u64

impl<E: Environment> ToLowerBitsBE for Field<E> {
    type Boolean = Boolean<E>;

    ///
    /// Outputs the lower `k` bits of an `n`-bit field element in big-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_be(&self, k: usize) -> Vec<Self::Boolean> {
        let mut bits_be = self.to_lower_bits_le(k);
        bits_be.reverse();
        bits_be
    }
}

impl<E: Environment> Metadata<dyn ToLowerBitsBE<Boolean = Boolean<E>>> for Field<E> {
    type Case = (CircuitType<Field<E>>, usize);
    type OutputType = Vec<CircuitType<Boolean<E>>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), k) => Count::is(*k as u64, 0, 0, 0),
            (_, k) => Count::is(0, 0, *k as u64, *k as u64 + 1),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(constant), k) => {
                constant.circuit().to_lower_bits_be(k).into_iter().map(CircuitType::from).collect()
            }
            (_, k) => vec![CircuitType::Private; k],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{bytes_from_bits_le, test_rng, FromBytes, ToBytes, UniformRand};

    const ITERATIONS: u64 = 100;

    // TODO: Fix these tests.

    #[rustfmt::skip]
    fn check_to_lower_k_bits_be<I: IntegerType + Unsigned + ToBytes>(
        mode: Mode,
    ) {
        let size_in_bits = <Circuit as Environment>::BaseField::size_in_bits();
        let size_in_bytes = (size_in_bits + 7) / 8;

        for i in 0..ITERATIONS {
            // Sample a random unsigned integer.
            let value: I = UniformRand::rand(&mut test_rng());
            let expected_bytes = value.to_bytes_le().unwrap();

            // Construct the unsigned integer as a field element.
            let candidate = {
                let mut field_bytes = bytes_from_bits_le(&expected_bytes.to_bits_le());
                field_bytes.resize(size_in_bytes, 0u8); // Pad up to byte size.
                Field::<Circuit>::new(mode, FromBytes::from_bytes_le(&field_bytes).unwrap())
            };

            Circuit::scope(&format!("{} {}", mode, i), || {
                let result = candidate.to_lower_bits_be(I::BITS as usize);
                assert_eq!(I::BITS, result.len() as u64);
                for (i, (expected_bit, candidate_bit)) in expected_bytes.to_bits_be().iter().zip_eq(result.iter()).enumerate() {
                    assert_eq!(*expected_bit, candidate_bit.eject_value(), "LSB+{}", i);
                }

                let case = (CircuitType::from(candidate), I::BITS as usize);
                assert_count!(ToLowerBitsBE<Boolean>() => Field, &case);
                assert_output_type!(ToLowerBitsBE<Boolean>() => Field, case, result);
            });
        }
    }

    // 8 bits

    #[test]
    fn test_to_8_bits_constant() {
        check_to_lower_k_bits_be::<u8>(Mode::Constant);
    }

    #[test]
    fn test_to_8_bits_public() {
        check_to_lower_k_bits_be::<u8>(Mode::Public);
    }

    #[test]
    fn test_to_8_bits_private() {
        check_to_lower_k_bits_be::<u8>(Mode::Private);
    }

    // 16 bits

    #[test]
    fn test_to_16_bits_constant() {
        check_to_lower_k_bits_be::<u16>(Mode::Constant);
    }

    #[test]
    fn test_to_16_bits_public() {
        check_to_lower_k_bits_be::<u16>(Mode::Public);
    }

    #[test]
    fn test_to_16_bits_private() {
        check_to_lower_k_bits_be::<u16>(Mode::Private);
    }

    // 32 bits

    #[test]
    fn test_to_32_bits_constant() {
        check_to_lower_k_bits_be::<u32>(Mode::Constant);
    }

    #[test]
    fn test_to_32_bits_public() {
        check_to_lower_k_bits_be::<u32>(Mode::Public);
    }

    #[test]
    fn test_to_32_bits_private() {
        check_to_lower_k_bits_be::<u32>(Mode::Private);
    }

    // 64 bits

    #[test]
    fn test_to_64_bits_constant() {
        check_to_lower_k_bits_be::<u64>(Mode::Constant);
    }

    #[test]
    fn test_to_64_bits_public() {
        check_to_lower_k_bits_be::<u64>(Mode::Public);
    }

    #[test]
    fn test_to_64_bits_private() {
        check_to_lower_k_bits_be::<u64>(Mode::Private);
    }

    // 128 bits

    #[test]
    fn test_to_128_bits_constant() {
        check_to_lower_k_bits_be::<u128>(Mode::Constant);
    }

    #[test]
    fn test_to_128_bits_public() {
        check_to_lower_k_bits_be::<u128>(Mode::Public);
    }

    #[test]
    fn test_to_128_bits_private() {
        check_to_lower_k_bits_be::<u128>(Mode::Private);
    }
}
