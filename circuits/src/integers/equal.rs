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
use crate::field::BaseField;

use itertools::Itertools;

impl<E: Environment, I: IntegerType> Equal<Self> for Integer<E, I> {
    type Boolean = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    fn is_eq(&self, other: &Self) -> Self::Boolean {
        // Determine if this operation is constant or variable.
        match self.is_constant() && other.is_constant() {
            true => self
                .bits_le
                .iter()
                .zip_eq(other.bits_le.iter())
                .map(|(this, that)| this.is_eq(that))
                .fold(Boolean::new(Mode::Constant, true), |a, b| a & b),
            false => {
                // Instead of comparing the bits of `self` and `other` directly, the integers are
                // converted into a field elements, and checked if they are equivalent as field elements.
                // Note: This is safe as the field is larger than the maximum integer type supported.
                let this = BaseField::from_bits_le(Mode::Private, &self.bits_le);
                let that = BaseField::from_bits_le(Mode::Private, &other.bits_le);
                this.is_eq(&that)
            }
        }
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    fn is_neq(&self, other: &Self) -> Self::Boolean {
        !self.is_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;
    use std::ops::RangeInclusive;

    const ITERATIONS: usize = 100;

    #[rustfmt::skip]
    fn check_equals<I: IntegerType>(
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
        let expected = first == second;
        let case = format!("({} == {})", first, second);

        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        check_operation_passes(&name, &case, expected, &a, &b, Integer::is_eq, num_constants, num_public, num_private, num_constraints);

        // Commute the operation.
        let a = Integer::<Circuit, I>::new(mode_a, second);
        let b = Integer::<Circuit, I>::new(mode_b, first);
        check_operation_passes(&name, &case, expected, &a, &b, Integer::is_eq, num_constants, num_public, num_private, num_constraints);
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
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let name = format!("Eq: {} == {} {}", mode_a, mode_b, i);
            check_equals(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
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
                let name = format!("Equals: ({} == {})", first, second);
                check_equals(
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
    fn test_u8_constant_equals_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_equals_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_constant_equals_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_public_equals_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_private_equals_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_public_equals_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_public_equals_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_private_equals_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u8_private_equals_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_equals_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_equals_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_constant_equals_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_public_equals_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_private_equals_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_public_equals_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_public_equals_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_private_equals_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i8_private_equals_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_equals_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_equals_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_constant_equals_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_public_equals_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_private_equals_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_public_equals_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_public_equals_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_private_equals_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u16_private_equals_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_equals_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_equals_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_constant_equals_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_public_equals_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_private_equals_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_public_equals_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_public_equals_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_private_equals_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i16_private_equals_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_equals_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_equals_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_constant_equals_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_public_equals_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_private_equals_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_public_equals_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_public_equals_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_private_equals_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u32_private_equals_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_equals_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_equals_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_constant_equals_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_public_equals_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_private_equals_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_public_equals_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_public_equals_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_private_equals_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i32_private_equals_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_equals_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_equals_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_constant_equals_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_public_equals_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_private_equals_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_public_equals_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_public_equals_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_private_equals_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u64_private_equals_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_equals_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_equals_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_constant_equals_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_public_equals_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_private_equals_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_public_equals_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_public_equals_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_private_equals_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i64_private_equals_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_equals_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_equals_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_constant_equals_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_public_equals_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_private_equals_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_public_equals_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_public_equals_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_private_equals_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_u128_private_equals_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_equals_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_equals_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_constant_equals_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_public_equals_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_private_equals_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_public_equals_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_public_equals_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_private_equals_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    fn test_i128_private_equals_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_equals_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_equals_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_equals_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_equals_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_equals_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_equals_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_equals_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_equals_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_equals_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_equals_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_equals_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_equals_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_equals_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_equals_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_equals_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_equals_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_equals_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 2, 0, 4, 5);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_equals_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 2, 0, 4, 5);
    }
}
