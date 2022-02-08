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

use super::*;

use itertools::Itertools;

impl<E: Environment, I: IntegerType> BitOr<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        self | &other
    }
}

impl<E: Environment, I: IntegerType> BitOr<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn bitor(self, other: Integer<E, I>) -> Self::Output {
        self | &other
    }
}

impl<E: Environment, I: IntegerType> BitOr<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn bitor(self, other: &Self) -> Self::Output {
        &self | other
    }
}

impl<E: Environment, I: IntegerType> BitOr<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn bitor(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output |= other;
        output
    }
}

impl<E: Environment, I: IntegerType> BitOrAssign<Integer<E, I>> for Integer<E, I> {
    fn bitor_assign(&mut self, other: Integer<E, I>) {
        *self |= &other;
    }
}

impl<E: Environment, I: IntegerType> BitOrAssign<&Integer<E, I>> for Integer<E, I> {
    fn bitor_assign(&mut self, other: &Integer<E, I>) {
        // Stores the bitwise OR of `self` and `other` in `self`.
        *self = Self {
            bits_le: self
                .bits_le
                .iter()
                .zip_eq(other.bits_le.iter())
                .map(|(self_bit, other_bit)| self_bit.or(other_bit))
                .collect(),
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_bitor<I: IntegerType, IC: IntegerTrait<Circuit, I>>(
        name: &str,
        expected: I,
        a: IC,
        b: IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let case = format!("({} | {})", a.eject_value(), b.eject_value());

            let candidate = a | b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + BitOr<Output = I>>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let name = format!("BitOr: ({} | {}) {}", mode_a, mode_b, i);
            let first : I = UniformRand::rand(&mut thread_rng());
            let second : I = UniformRand::rand(&mut thread_rng());

            let expected = first | second;
            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::<Circuit, I>::new(mode_b, second);

            check_bitor::<I, Integer<Circuit, I>>(&name, expected, a, b, num_constants, num_public, num_private, num_constraints);
        }

        // Closure for checking particular corner cases.
        let check_bitor = | first, second, expected | {
            let name = format!("BitOr: ({} | {})", first, second);
            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::<Circuit, I>::new(mode_b, second);

            check_bitor::<I, Integer<Circuit, I>>(&name, expected, a, b, num_constants, num_public, num_private, num_constraints);
        };

        // Check cases common to signed and unsigned integers.
        check_bitor(I::zero(), I::MAX, I::MAX);
        check_bitor(I::MAX, I::zero(), I::MAX);
        check_bitor(I::zero(), I::MIN, I::MIN);
        check_bitor(I::MIN, I::zero(), I::MIN);

        // Check cases specific to signed and unsigned integers respectively.
        for _i in 0..ITERATIONS {
            let other: I = UniformRand::rand(&mut thread_rng());
            if I::is_signed() {
                check_bitor(I::zero() - I::one(), other, I::zero() - I::one());
            } else {
                check_bitor(I::MAX, other, I::MAX);
            }
        }
    }

    // Tests for u8

    #[test]
    fn test_u8_constant_bitor_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_bitor_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_bitor_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_bitor_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_bitor_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_bitor_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_public_bitor_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_private_bitor_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_private_bitor_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_bitor_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_bitor_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_bitor_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_bitor_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_bitor_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_bitor_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_public_bitor_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_private_bitor_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_private_bitor_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_bitor_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_bitor_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_bitor_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_bitor_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_bitor_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_bitor_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_public_bitor_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_private_bitor_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_private_bitor_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_bitor_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_bitor_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_bitor_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_bitor_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_bitor_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_bitor_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_public_bitor_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_private_bitor_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_private_bitor_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_bitor_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_bitor_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_bitor_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_bitor_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_bitor_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_bitor_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_public_bitor_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_private_bitor_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_private_bitor_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_bitor_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_bitor_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_bitor_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_bitor_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_bitor_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_bitor_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_public_bitor_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_private_bitor_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_private_bitor_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_bitor_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_bitor_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_bitor_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_bitor_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_bitor_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_bitor_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_public_bitor_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_private_bitor_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_private_bitor_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_bitor_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_bitor_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_bitor_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_bitor_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_bitor_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_bitor_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_public_bitor_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_private_bitor_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_private_bitor_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_bitor_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_bitor_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_bitor_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_bitor_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_bitor_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_bitor_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_public_bitor_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_private_bitor_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_private_bitor_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 128, 128);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_bitor_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_bitor_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_bitor_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_bitor_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_bitor_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_bitor_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_public_bitor_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_private_bitor_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_private_bitor_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 128, 128);
    }
}
