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

impl<E: Environment> ToUpperBitsLE for Field<E> {
    type Boolean = Boolean<E>;

    ///
    /// Outputs the upper `k` bits of an `n`-bit field element in little-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_le(&self, k: usize) -> Vec<Self::Boolean> {
        let mut bits_le = self.to_upper_bits_be(k);
        bits_le.reverse();
        bits_le
    }
}

impl<E: Environment> Metadata<dyn ToUpperBitsLE<Boolean = Boolean<E>>> for Field<E> {
    type Case = (CircuitType<Field<E>>, usize);
    type OutputType = CircuitType<Vec<Boolean<E>>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), k) => Count::is(*k as u64, 0, 0, 0),
            (_, k) => Count::is(0, 0, *k as u64, *k as u64 + 1),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(constant), k) => CircuitType::from(constant.circuit().to_upper_bits_le(k)),
            _ => CircuitType::Private,
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
    fn check_to_upper_k_bits_le<I: IntegerType + Unsigned + ToBytes>(
        mode: Mode,
    ) {
        let size_in_bits = <Circuit as Environment>::BaseField::size_in_bits();
        let size_in_bytes = (size_in_bits + 7) / 8;
        let num_leading_zero_bits = (size_in_bytes * 8) - size_in_bits;

        for i in 0..ITERATIONS {
            // Sample a random unsigned integer.
            let value: I = UniformRand::rand(&mut test_rng());
            let expected = value.to_bytes_le().unwrap().to_bits_le();

            // Construct the unsigned integer as a field element.
            let candidate = {
                //
                // Restructure the value as field element as follows.
                //
                // MSB | MSB-1 | MSB-2 | MSB-3 | MSB-4 | ... | MSB-k | MSB-k-1 | ... | LSB
                // ------------------------------------------------------------------------
                //  0  |   0   |   0   |   0   |  b_k  | ... |  b_0  |    0    | ... |  0
                //
                // For advanced readers: We extend the leading zeros one-past `MODULUS_BITS`
                // to ensure `CAPACITY` is always satisfied for testing.
                //
                let field_bytes = {
                    let mut field_bits_le_with_leading_zeros = vec![false; num_leading_zero_bits + 1];
                    for bit in &expected {
                        field_bits_le_with_leading_zeros.push(*bit);
                    }
                    field_bits_le_with_leading_zeros.resize(size_in_bytes * 8, false); // Pad up to field byte-aligned size.

                    let mut field_bits_le_with_leading_zeros = field_bits_le_with_leading_zeros;
                    field_bits_le_with_leading_zeros.reverse();

                    bytes_from_bits_le(&field_bits_le_with_leading_zeros)
                };
                Field::<Circuit>::new(mode, FromBytes::from_bytes_le(&field_bytes).unwrap())
            };

            Circuit::scope(&format!("{} {}", mode, i), || {
                let num_bits_with_capacity = I::BITS + 1;
                let result = candidate.to_upper_bits_le(num_bits_with_capacity as usize);
                assert_eq!(num_bits_with_capacity, result.len() as u64);
                for (i, (expected_bit, candidate_bit)) in expected.iter().zip_eq(result.iter().skip(1)).enumerate() {
                    assert_eq!(*expected_bit, candidate_bit.eject_value(), "MSB-{}", i);
                }

                let case = (CircuitType::from(candidate), num_bits_with_capacity as usize);
                assert_count!(ToUpperBits<Boolean>() => Field, &case);
                assert_output_type!(ToUpperBits<Boolean>() => Field, case, result);
            });
        }
    }

    // 8 bits

    #[test]
    fn test_to_8_bits_constant() {
        check_to_upper_k_bits_le::<u8>(Mode::Constant); // This actually tests 9 bits.
    }

    #[test]
    fn test_to_8_bits_public() {
        check_to_upper_k_bits_le::<u8>(Mode::Public); // This actually tests 9 bits.
    }

    #[test]
    fn test_to_8_bits_private() {
        check_to_upper_k_bits_le::<u8>(Mode::Private); // This actually tests 9 bits.
    }

    // 16 bits

    #[test]
    fn test_to_16_bits_constant() {
        check_to_upper_k_bits_le::<u16>(Mode::Constant); // This actually tests 17 bits.
    }

    #[test]
    fn test_to_16_bits_public() {
        check_to_upper_k_bits_le::<u16>(Mode::Public); // This actually tests 17 bits.
    }

    #[test]
    fn test_to_16_bits_private() {
        check_to_upper_k_bits_le::<u16>(Mode::Private); // This actually tests 17 bits.
    }

    // 32 bits

    #[test]
    fn test_to_32_bits_constant() {
        check_to_upper_k_bits_le::<u32>(Mode::Constant); // This actually tests 33 bits.
    }

    #[test]
    fn test_to_32_bits_public() {
        check_to_upper_k_bits_le::<u32>(Mode::Public); // This actually tests 33 bits.
    }

    #[test]
    fn test_to_32_bits_private() {
        check_to_upper_k_bits_le::<u32>(Mode::Private); // This actually tests 33 bits.
    }

    // 64 bits

    #[test]
    fn test_to_64_bits_constant() {
        check_to_upper_k_bits_le::<u64>(Mode::Constant); // This actually tests 65 bits.
    }

    #[test]
    fn test_to_64_bits_public() {
        check_to_upper_k_bits_le::<u64>(Mode::Public); // This actually tests 65 bits.
    }

    #[test]
    fn test_to_64_bits_private() {
        check_to_upper_k_bits_le::<u64>(Mode::Private); // This actually tests 65 bits.
    }

    // 128 bits

    #[test]
    fn test_to_128_bits_constant() {
        check_to_upper_k_bits_le::<u128>(Mode::Constant); // This actually tests 129 bits.
    }

    #[test]
    fn test_to_128_bits_public() {
        check_to_upper_k_bits_le::<u128>(Mode::Public); // This actually tests 129 bits.
    }

    #[test]
    fn test_to_128_bits_private() {
        check_to_upper_k_bits_le::<u128>(Mode::Private); // This actually tests 129 bits.
    }
}
