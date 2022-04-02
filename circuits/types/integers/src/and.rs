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
use snarkvm_circuits_environment::{Metric, MetricForOperation};

impl<E: Environment, I: IntegerType> BitAnd<Integer<E, I>> for Integer<E, I> {
    type Output = Integer<E, I>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: Integer<E, I>) -> Self::Output {
        self & &other
    }
}

impl<E: Environment, I: IntegerType> BitAnd<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: Integer<E, I>) -> Self::Output {
        self & &other
    }
}

impl<E: Environment, I: IntegerType> BitAnd<&Integer<E, I>> for Integer<E, I> {
    type Output = Integer<E, I>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: &Integer<E, I>) -> Self::Output {
        &self & other
    }
}

impl<E: Environment, I: IntegerType> BitAnd<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output &= other;
        output
    }
}

impl<E: Environment, I: IntegerType> BitAndAssign<Integer<E, I>> for Integer<E, I> {
    /// Sets `self` as `(self AND other)`.
    fn bitand_assign(&mut self, other: Integer<E, I>) {
        *self &= &other;
    }
}

impl<E: Environment, I: IntegerType> BitAndAssign<&Integer<E, I>> for Integer<E, I> {
    /// Sets `self` as `(self AND other)`.
    fn bitand_assign(&mut self, other: &Integer<E, I>) {
        // Stores the bitwise AND of `self` and `other` in `self`.
        *self = Self {
            bits_le: self.bits_le.iter().zip_eq(other.bits_le.iter()).map(|(a, b)| a & b).collect(),
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::ops::RangeInclusive;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_and<I: IntegerType + BitAnd<Output = I>>(
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
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let case = format!("BitAnd: ({} & {})", first, second);
        let expected = first & second;
        check_operation_passes(name, &case, expected, &a, &b, |a: &Integer<Circuit, I>, b: &Integer<Circuit, I> | { a.bitand(b) }, num_constants, num_public, num_private, num_constraints);
        // Commute the operation.
        let a = Integer::<Circuit, I>::new(mode_a, second);
        let b = Integer::<Circuit, I>::new(mode_b, first);
        check_operation_passes(name, &case, expected, &a, &b, |a: &Integer<Circuit, I>, b: &Integer<Circuit, I> | { a.bitand(b) }, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + BitAnd<Output = I>>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_bitand = | name: &str, first: I, second: I | check_and(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            let first : I = UniformRand::rand(&mut test_rng());
            let second : I = UniformRand::rand(&mut test_rng());

            let name = format!("BitAnd: ({} & {}) {}", mode_a, mode_b, i);
            check_bitand(&name, first, second);

            let name = format!("BitAnd Identity: ({} & {}) {}", mode_a, mode_b, i);
            let identity_element = if I::is_signed() { I::zero() - I::one() } else { I::MAX };
            check_bitand(&name, identity_element, first);
        }

        // Check cases common to signed and unsigned integers.
        check_bitand("0 & MAX", I::zero(), I::MAX);
        check_bitand("MAX & 0", I::MAX, I::zero());
        check_bitand("0 & MIN", I::zero(), I::MIN);
        check_bitand("MIN & 0", I::MIN, I::zero());
    }

    fn run_exhaustive_test<I: IntegerType + BitAnd<Output = I>>(
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
                let name = format!("BitAnd: ({} & {})", first, second);
                check_and(
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

    // Tests for u8

    #[test]
    fn test_u8_constant_bitand_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_bitand_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_bitand_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_bitand_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_bitand_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_bitand_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_public_bitand_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_private_bitand_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_private_bitand_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_bitand_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_bitand_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_bitand_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_bitand_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_bitand_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_bitand_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_public_bitand_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_private_bitand_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_private_bitand_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_bitand_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_bitand_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_bitand_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_bitand_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_bitand_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_bitand_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_public_bitand_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_private_bitand_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_private_bitand_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_bitand_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_bitand_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_bitand_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_bitand_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_bitand_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_bitand_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_public_bitand_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_private_bitand_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_private_bitand_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 16, 16);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_bitand_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_bitand_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_bitand_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_bitand_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_bitand_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_bitand_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_public_bitand_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_private_bitand_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_private_bitand_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_bitand_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_bitand_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_bitand_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_bitand_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_bitand_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_bitand_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_public_bitand_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_private_bitand_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_private_bitand_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 32, 32);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_bitand_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_bitand_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_bitand_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_bitand_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_bitand_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_bitand_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_public_bitand_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_private_bitand_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_private_bitand_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_bitand_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_bitand_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_bitand_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_bitand_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_bitand_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_bitand_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_public_bitand_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_private_bitand_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_private_bitand_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 64, 64);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_bitand_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_bitand_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_bitand_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_bitand_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_bitand_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_bitand_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_public_bitand_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_private_bitand_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_private_bitand_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 128, 128);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_bitand_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_bitand_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_bitand_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_bitand_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_bitand_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_bitand_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_public_bitand_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_private_bitand_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_private_bitand_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 128, 128);
    }

    // Exhaustive tests for u8

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_bitand_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_bitand_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_bitand_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_bitand_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_bitand_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_bitand_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_bitand_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_bitand_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_bitand_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 8, 8);
    }

    // Exhaustive tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_bitand_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_bitand_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_bitand_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_bitand_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_bitand_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_bitand_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_bitand_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_bitand_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 8, 8);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_bitand_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 8, 8);
    }
}
