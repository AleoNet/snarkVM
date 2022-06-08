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

impl<E: Environment, I: IntegerType> ToBits for Integer<E, I> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self` *with* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_le()
    }

    /// Outputs the big-endian bit representation of `self` *with* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_be()
    }
}

impl<E: Environment, I: IntegerType> ToBits for &Integer<E, I> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self` *with* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.bits_le.clone()
    }

    /// Outputs the big-endian bit representation of `self` *with* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_le = self.to_bits_le();
        bits_le.reverse();
        bits_le
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 128;

    fn check_to_bits_le<I: IntegerType>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_bits_le();
                assert_eq!(I::BITS, candidate.len() as u64);

                // Ensure every bit matches.
                let mut expected = expected.to_le();
                for candidate_bit in candidate {
                    assert_eq!(expected & I::one() == I::one(), candidate_bit.eject_value());
                    expected = expected.wrapping_shr(1);
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_to_bits_be<I: IntegerType>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_bits_be();
                assert_eq!(I::BITS, candidate.len() as u64);

                // Ensure every bit matches.
                let mut expected = expected.to_le();
                for candidate_bit in candidate.iter().rev() {
                    assert_eq!(expected & I::one() == I::one(), candidate_bit.eject_value());
                    expected = expected.wrapping_shr(1);
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    /// Checks that the field element, when converted to little-endian bits, is well-formed.
    fn check_individual_bits_le<I: IntegerType>(candidate: Integer<Circuit, I>) {
        for (i, bit) in candidate.to_bits_le().iter().enumerate() {
            match i == 0 {
                true => assert!(bit.eject_value()),
                false => assert!(!bit.eject_value()),
            }
        }
    }

    /// Checks that the field element, when converted to big-endian bits, is well-formed.
    fn check_individual_bits_be<I: IntegerType>(candidate: Integer<Circuit, I>) {
        for (i, bit) in candidate.to_bits_be().iter().rev().enumerate() {
            match i == 0 {
                true => assert!(bit.eject_value()),
                false => assert!(!bit.eject_value()),
            }
        }
    }

    fn test_individual_bits<I: IntegerType>(value: console::Integer<<Circuit as Environment>::Network, I>) {
        // Constant
        check_individual_bits_le(Integer::<Circuit, I>::new(Mode::Constant, value));
        check_individual_bits_be(Integer::<Circuit, I>::new(Mode::Constant, value));
        // Public
        check_individual_bits_le(Integer::<Circuit, I>::new(Mode::Public, value));
        check_individual_bits_be(Integer::<Circuit, I>::new(Mode::Public, value));
        // Private
        check_individual_bits_le(Integer::<Circuit, I>::new(Mode::Private, value));
        check_individual_bits_be(Integer::<Circuit, I>::new(Mode::Private, value));
    }

    // Tests for u8.

    #[test]
    fn test_u8_to_bits_le_constant() {
        type I = u8;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_to_bits_le_public() {
        type I = u8;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_to_bits_le_private() {
        type I = u8;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_to_bits_be_constant() {
        type I = u8;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_to_bits_be_public() {
        type I = u8;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_to_bits_be_private() {
        type I = u8;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i8.

    #[test]
    fn test_i8_to_bits_le_constant() {
        type I = i8;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_to_bits_le_public() {
        type I = i8;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_to_bits_le_private() {
        type I = i8;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_to_bits_be_constant() {
        type I = i8;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_to_bits_be_public() {
        type I = i8;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_to_bits_be_private() {
        type I = i8;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u16.

    #[test]
    fn test_u16_to_bits_le_constant() {
        type I = u16;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_to_bits_le_public() {
        type I = u16;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_to_bits_le_private() {
        type I = u16;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_to_bits_be_constant() {
        type I = u16;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_to_bits_be_public() {
        type I = u16;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_to_bits_be_private() {
        type I = u16;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i16.

    #[test]
    fn test_i16_to_bits_le_constant() {
        type I = i16;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_to_bits_le_public() {
        type I = i16;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_to_bits_le_private() {
        type I = i16;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_to_bits_be_constant() {
        type I = i16;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_to_bits_be_public() {
        type I = i16;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_to_bits_be_private() {
        type I = i16;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u32.

    #[test]
    fn test_u32_to_bits_le_constant() {
        type I = u32;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_to_bits_le_public() {
        type I = u32;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_to_bits_le_private() {
        type I = u32;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_to_bits_be_constant() {
        type I = u32;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_to_bits_be_public() {
        type I = u32;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_to_bits_be_private() {
        type I = u32;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i32.

    #[test]
    fn test_i32_to_bits_le_constant() {
        type I = i32;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_to_bits_le_public() {
        type I = i32;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_to_bits_le_private() {
        type I = i32;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_to_bits_be_constant() {
        type I = i32;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_to_bits_be_public() {
        type I = i32;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_to_bits_be_private() {
        type I = i32;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u64.

    #[test]
    fn test_u64_to_bits_le_constant() {
        type I = u64;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_to_bits_le_public() {
        type I = u64;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_to_bits_le_private() {
        type I = u64;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_to_bits_be_constant() {
        type I = u64;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_to_bits_be_public() {
        type I = u64;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_to_bits_be_private() {
        type I = u64;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i64.

    #[test]
    fn test_i64_to_bits_le_constant() {
        type I = i64;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_to_bits_le_public() {
        type I = i64;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_to_bits_le_private() {
        type I = i64;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_to_bits_be_constant() {
        type I = i64;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_to_bits_be_public() {
        type I = i64;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_to_bits_be_private() {
        type I = i64;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u128.

    #[test]
    fn test_u128_to_bits_le_constant() {
        type I = u128;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_to_bits_le_public() {
        type I = u128;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_to_bits_le_private() {
        type I = u128;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_to_bits_be_constant() {
        type I = u128;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_to_bits_be_public() {
        type I = u128;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_to_bits_be_private() {
        type I = u128;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i128.

    #[test]
    fn test_i128_to_bits_le_constant() {
        type I = i128;
        check_to_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_to_bits_le_public() {
        type I = i128;
        check_to_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_to_bits_le_private() {
        type I = i128;
        check_to_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_to_bits_be_constant() {
        type I = i128;
        check_to_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_to_bits_be_public() {
        type I = i128;
        check_to_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_to_bits_be_private() {
        type I = i128;
        check_to_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_one() {
        type I = u8;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_i8_one() {
        type I = i8;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_u16_one() {
        type I = u16;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_i16_one() {
        type I = i16;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_u32_one() {
        type I = u32;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_i32_one() {
        type I = i32;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_u64_one() {
        type I = u64;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_i64_one() {
        type I = i64;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_u128_one() {
        type I = u128;
        test_individual_bits::<I>(console::Integer::one());
    }

    #[test]
    fn test_i128_one() {
        type I = i128;
        test_individual_bits::<I>(console::Integer::one());
    }
}
