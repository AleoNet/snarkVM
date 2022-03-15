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

impl<E: Environment, I: IntegerType> Compare<Self> for Integer<E, I> {
    type Boolean = Boolean<E>;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Self) -> Self::Boolean {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the comparison and return the new constant.
            Self::Boolean::new(Mode::Constant, self.eject_value().le(&other.eject_value()))
        } else {
            // Compute the less than operation via an overflow check.
            // If I::MAX + a - b + 1 overflows, then a >= b, otherwise a < b.
            let max_plus_difference_plus_one =
                Self::new(Mode::Constant, I::MAX).to_field() + self.to_field() - other.to_field() + Field::one();
            match max_plus_difference_plus_one.to_lower_bits_le(I::BITS + 1).last() {
                Some(bit) => !bit,
                None => E::halt("Malformed expression detected during integer comparison."),
            }
        }
    }

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Self) -> Self::Boolean {
        other.is_less_than(self)
    }

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Self) -> Self::Boolean {
        other.is_greater_than_or_equal(self)
    }

    /// Returns `true` if `self` is greater than or equal to `other`.
    fn is_greater_than_or_equal(&self, other: &Self) -> Self::Boolean {
        !self.is_less_than(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::ops::RangeInclusive;

    const ITERATIONS: usize = 100;

    #[rustfmt::skip]
    fn check_compare<I: IntegerType>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Check `is_less_than`.
        let expected = first < second;
        let case = format!("({} < {})", first, second);

        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        check_operation_passes(name, &case, expected, &a, &b, Integer::is_less_than, num_constants, num_public, num_private, num_constraints);

        // Check `is_less_than_or_equal`
        let expected = first <= second;
        let case = format!("({} <= {})", first, second);

        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        check_operation_passes(name, &case, expected, &a, &b, Integer::is_less_than_or_equal, num_constants, num_public, num_private, num_constraints);

        // Check `is_greater_than`
        let expected = first > second;
        let case = format!("({} > {})", first, second);

        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        check_operation_passes(name, &case, expected, &a, &b, Integer::is_greater_than, num_constants, num_public, num_private, num_constraints);

        // Check `is_greater_than_or_equal`
        let expected = first > second;
        let case = format!("({} >= {})", first, second);

        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        check_operation_passes(name, &case, expected, &a, &b, Integer::is_greater_than_or_equal, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Compare: {}, {}, {}", mode_a, mode_b, i);
            check_compare(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        }
    }

    fn run_exhaustive_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Compare: ({}, {})", first, second);
                check_compare(
                    &name,
                    first,
                    second,
                    mode_a,
                    mode_b,
                    num_constants,
                    num_public,
                    num_private,
                    num_constraints,
                );
            }
        }
    }

    #[test]
    fn test_u8_constant_compare_with_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_compare_with_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_constant_compare_with_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_public_compare_with_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_private_compare_with_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_public_compare_with_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_public_compare_with_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_private_compare_with_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u8_private_compare_with_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_compare_with_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_compare_with_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_constant_compare_with_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_public_compare_with_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_private_compare_with_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_public_compare_with_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_public_compare_with_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_private_compare_with_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i8_private_compare_with_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_compare_with_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_compare_with_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_constant_compare_with_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_public_compare_with_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_private_compare_with_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_public_compare_with_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_public_compare_with_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_private_compare_with_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u16_private_compare_with_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_compare_with_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_compare_with_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_constant_compare_with_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_public_compare_with_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_private_compare_with_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_public_compare_with_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_public_compare_with_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_private_compare_with_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i16_private_compare_with_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_compare_with_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_compare_with_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_constant_compare_with_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_public_compare_with_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_private_compare_with_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_public_compare_with_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_public_compare_with_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_private_compare_with_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u32_private_compare_with_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_compare_with_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_compare_with_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_constant_compare_with_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_public_compare_with_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_private_compare_with_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_public_compare_with_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_public_compare_with_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_private_compare_with_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i32_private_compare_with_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_compare_with_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_compare_with_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_constant_compare_with_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_public_compare_with_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_private_compare_with_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_public_compare_with_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_public_compare_with_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_private_compare_with_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u64_private_compare_with_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_compare_with_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_compare_with_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_constant_compare_with_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_public_compare_with_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_private_compare_with_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_public_compare_with_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_public_compare_with_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_private_compare_with_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i64_private_compare_with_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_compare_with_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_compare_with_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_constant_compare_with_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_public_compare_with_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_private_compare_with_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_public_compare_with_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_public_compare_with_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_private_compare_with_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_u128_private_compare_with_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_compare_with_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_compare_with_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_constant_compare_with_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_public_compare_with_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_private_compare_with_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_public_compare_with_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_public_compare_with_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_private_compare_with_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    fn test_i128_private_compare_with_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_compare_with_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_compare_with_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_compare_with_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_compare_with_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_compare_with_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_compare_with_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_compare_with_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_compare_with_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_compare_with_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_compare_with_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_compare_with_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_compare_with_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_compare_with_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_compare_with_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_compare_with_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_compare_with_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_compare_with_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 2, 3);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_compare_with_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 2, 3);
    }
}
