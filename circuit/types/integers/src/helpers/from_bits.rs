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

impl<E: Environment, I: IntegerType> FromBits for Integer<E, I> {
    type Boolean = Boolean<E>;

    /// Initializes a new integer from a list of little-endian bits *with* trailing zeros.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Ensure the list of booleans is within the allowed size in bits.
        let num_bits = bits_le.len() as u64;
        if num_bits > I::BITS {
            // Check if all excess bits are zero.
            let should_be_zero =
                bits_le[I::BITS as usize..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit);
            // Ensure `should_be_zero` is zero.
            E::assert_eq(E::zero(), should_be_zero);
        }

        // Construct the sanitized list of bits, resizing up if necessary.
        let mut bits_le = bits_le.iter().take(I::BITS as usize).cloned().collect::<Vec<_>>();
        bits_le.resize(I::BITS as usize, Boolean::constant(false));

        Self { bits_le, phantom: Default::default() }
    }

    /// Initializes a new integer from a list of big-endian bits *with* leading zeros.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(&bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 128;

    fn check_from_bits_le<I: IntegerType>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Uniform::rand(&mut test_rng());
            let given_bits = Integer::<Circuit, I>::new(mode, expected).to_bits_le();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_le(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![given_bits, vec![Boolean::new(mode, false); i as usize]].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_le(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });
        }
    }

    fn check_from_bits_be<I: IntegerType>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Uniform::rand(&mut test_rng());
            let given_bits = Integer::<Circuit, I>::new(mode, expected).to_bits_be();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![vec![Boolean::new(mode, false); i as usize], given_bits].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_be(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });
        }
    }

    // Tests for u8.

    #[test]
    fn test_u8_from_bits_le_constant() {
        type I = u8;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_from_bits_le_public() {
        type I = u8;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_from_bits_le_private() {
        type I = u8;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_from_bits_be_constant() {
        type I = u8;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_from_bits_be_public() {
        type I = u8;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_from_bits_be_private() {
        type I = u8;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i8.

    #[test]
    fn test_i8_from_bits_le_constant() {
        type I = i8;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_from_bits_le_public() {
        type I = i8;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_from_bits_le_private() {
        type I = i8;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_from_bits_be_constant() {
        type I = i8;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_from_bits_be_public() {
        type I = i8;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_from_bits_be_private() {
        type I = i8;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u16.

    #[test]
    fn test_u16_from_bits_le_constant() {
        type I = u16;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_from_bits_le_public() {
        type I = u16;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_from_bits_le_private() {
        type I = u16;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_from_bits_be_constant() {
        type I = u16;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_from_bits_be_public() {
        type I = u16;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_from_bits_be_private() {
        type I = u16;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i16.

    #[test]
    fn test_i16_from_bits_le_constant() {
        type I = i16;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_from_bits_le_public() {
        type I = i16;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_from_bits_le_private() {
        type I = i16;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_from_bits_be_constant() {
        type I = i16;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_from_bits_be_public() {
        type I = i16;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_from_bits_be_private() {
        type I = i16;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u32.

    #[test]
    fn test_u32_from_bits_le_constant() {
        type I = u32;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_from_bits_le_public() {
        type I = u32;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_from_bits_le_private() {
        type I = u32;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_from_bits_be_constant() {
        type I = u32;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_from_bits_be_public() {
        type I = u32;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_from_bits_be_private() {
        type I = u32;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i32.

    #[test]
    fn test_i32_from_bits_le_constant() {
        type I = i32;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_from_bits_le_public() {
        type I = i32;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_from_bits_le_private() {
        type I = i32;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_from_bits_be_constant() {
        type I = i32;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_from_bits_be_public() {
        type I = i32;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_from_bits_be_private() {
        type I = i32;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u64.

    #[test]
    fn test_u64_from_bits_le_constant() {
        type I = u64;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_from_bits_le_public() {
        type I = u64;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_from_bits_le_private() {
        type I = u64;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_from_bits_be_constant() {
        type I = u64;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_from_bits_be_public() {
        type I = u64;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_from_bits_be_private() {
        type I = u64;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i64.

    #[test]
    fn test_i64_from_bits_le_constant() {
        type I = i64;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_from_bits_le_public() {
        type I = i64;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_from_bits_le_private() {
        type I = i64;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_from_bits_be_constant() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_from_bits_be_public() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_from_bits_be_private() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for u128.

    #[test]
    fn test_u128_from_bits_le_constant() {
        type I = u128;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_from_bits_le_public() {
        type I = u128;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_from_bits_le_private() {
        type I = u128;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_from_bits_be_constant() {
        type I = u128;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_from_bits_be_public() {
        type I = u128;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_from_bits_be_private() {
        type I = u128;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }

    // Tests for i128.

    #[test]
    fn test_i128_from_bits_le_constant() {
        type I = i128;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_from_bits_le_public() {
        type I = i128;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_from_bits_le_private() {
        type I = i128;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_from_bits_be_constant() {
        type I = i128;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_from_bits_be_public() {
        type I = i128;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_from_bits_be_private() {
        type I = i128;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }
}
