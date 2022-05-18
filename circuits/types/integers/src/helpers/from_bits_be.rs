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

impl<E: Environment, I: IntegerType> FromBitsBE for Integer<E, I> {
    type Boolean = Boolean<E>;

    /// Initializes a new integer from a list of big-endian bits *with* leading zeros.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(&bits_le)
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn FromBitsBE<Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = Vec<CircuitType<Boolean<E>>>;
    type OutputType = IntegerCircuitType<E, I>;

    fn count(case: &Self::Case) -> Count {
        count!(Integer<E, I>, FromBitsLE<Boolean = Boolean<E>>, case)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let mut bits_le = case;
        bits_le.reverse();

        output_type!(Self, FromBitsLE<Boolean = Boolean<E>>, bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 128;

    fn check_from_bits_be<I: IntegerType>(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random integer.
            let expected: I = UniformRand::rand(&mut test_rng());
            let given_bits = Integer::<Circuit, I>::new(mode, expected).to_bits_be();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());

                let case = given_bits.iter().map(CircuitType::from).collect();
                assert_count!(Integer<Circuit, I>, FromBitsBE<Boolean = Boolean<Circuit>>, &case);
                assert_output_type!(Integer<Circuit, I>, FromBitsBE<Boolean = Boolean<Circuit>>, case, candidate);
            });

            // Add excess zero bits.
            let given_bits = vec![vec![Boolean::new(mode, false); i as usize], given_bits].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());

                let case = given_bits.iter().map(CircuitType::from).collect();
                assert_count!(Integer<Circuit, I>, FromBitsBE<Boolean = Boolean<Circuit>>, &case);
                assert_output_type!(Integer<Circuit, I>, FromBitsBE<Boolean = Boolean<Circuit>>, case, candidate);
            });
        }
    }

    // Tests for u8.

    #[test]
    fn test_u8_from_bits_be_constant() {
        type I = u8;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_u8_from_bits_be_public() {
        type I = u8;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_u8_from_bits_be_private() {
        type I = u8;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for i8.

    #[test]
    fn test_i8_from_bits_be_constant() {
        type I = i8;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_i8_from_bits_be_public() {
        type I = i8;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_i8_from_bits_be_private() {
        type I = i8;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for u16.

    #[test]
    fn test_u16_from_bits_be_constant() {
        type I = u16;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_u16_from_bits_be_public() {
        type I = u16;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_u16_from_bits_be_private() {
        type I = u16;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for i16.

    #[test]
    fn test_i16_from_bits_be_constant() {
        type I = i16;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_i16_from_bits_be_public() {
        type I = i16;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_i16_from_bits_be_private() {
        type I = i16;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for u32.

    #[test]
    fn test_u32_from_bits_be_constant() {
        type I = u32;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_u32_from_bits_be_public() {
        type I = u32;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_u32_from_bits_be_private() {
        type I = u32;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for i32.

    #[test]
    fn test_i32_from_bits_be_constant() {
        type I = i32;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_i32_from_bits_be_public() {
        type I = i32;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_i32_from_bits_be_private() {
        type I = i32;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for u64.

    #[test]
    fn test_u64_from_bits_be_constant() {
        type I = u64;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_u64_from_bits_be_public() {
        type I = u64;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_u64_from_bits_be_private() {
        type I = u64;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for i64.

    #[test]
    fn test_i64_from_bits_be_constant() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_i64_from_bits_be_public() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_i64_from_bits_be_private() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for u128.

    #[test]
    fn test_u128_from_bits_be_constant() {
        type I = u128;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_u128_from_bits_be_public() {
        type I = u128;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_u128_from_bits_be_private() {
        type I = u128;
        check_from_bits_be::<I>(Mode::Private);
    }

    // Tests for i128.

    #[test]
    fn test_i128_from_bits_be_constant() {
        type I = i128;
        check_from_bits_be::<I>(Mode::Constant);
    }

    #[test]
    fn test_i128_from_bits_be_public() {
        type I = i128;
        check_from_bits_be::<I>(Mode::Public);
    }

    #[test]
    fn test_i128_from_bits_be_private() {
        type I = i128;
        check_from_bits_be::<I>(Mode::Private);
    }
}
