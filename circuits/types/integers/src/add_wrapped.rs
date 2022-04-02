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

impl<E: Environment, I: IntegerType> AddWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_add(&other.eject_value()))
        } else {
            // Instead of adding the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and summed, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let sum = self.to_field() + other.to_field();

            // Extract the integer bits from the field element, with a carry bit.
            let mut bits_le = sum.to_lower_bits_le(I::BITS + 1);
            // Drop the carry bit as the operation is wrapped addition.
            bits_le.pop();

            // Return the sum of `self` and `other`.
            Integer { bits_le, phantom: Default::default() }
        }
    }
}

impl<E: Environment, I: IntegerType> Operation<Integer<E, I>>
    for dyn AddWrapped<Integer<E, I>, Output = Integer<E, I>>
{
    type Input = (Integer<E, I>, Integer<E, I>);
    type Output = Integer<E, I>;

    fn invoke(input: Self::Input) -> Self::Output {
        input.0.add_wrapped(&input.1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use core::ops::RangeInclusive;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_add<I: IntegerType>(
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
        let case = format!("({} + {})", a.eject_value(), b.eject_value());
        let expected = first.wrapping_add(&second);
        check_operation_passes(name, &case, expected, &a, &b, Integer::add_wrapped, num_constants, num_public, num_private, num_constraints);
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

            let name = format!("Add: {} + {} {}", mode_a, mode_b, i);
            check_add(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

            let name = format!("Add: {} + {} {} (commutative)", mode_a, mode_b, i);
            check_add(&name, second, first, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        }

        // Overflow
        check_add("MAX + 1", I::MAX, I::one(), mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        check_add("1 + MAX", I::one(), I::MAX, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        // Underflow
        if I::is_signed() {
            check_add("MIN + (-1)", I::MIN, I::zero() - I::one(), mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            check_add("-1 + MIN", I::zero() - I::one(), I::MIN, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Add: ({} + {})", first, second);
                check_add(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_plus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_plus_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_constant_plus_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_public_plus_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_private_plus_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_public_plus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_public_plus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_private_plus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    fn test_u8_private_plus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 9, 10);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_plus_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_plus_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_constant_plus_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_public_plus_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_private_plus_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_public_plus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_public_plus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_private_plus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    fn test_i8_private_plus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 9, 10);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_plus_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_plus_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_constant_plus_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_public_plus_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_private_plus_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_public_plus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_public_plus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_private_plus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_u16_private_plus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 17, 18);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_plus_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_plus_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_constant_plus_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_public_plus_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_private_plus_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_public_plus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_public_plus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_private_plus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_i16_private_plus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 17, 18);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_plus_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_plus_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_constant_plus_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_public_plus_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_private_plus_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_public_plus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_public_plus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_private_plus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_u32_private_plus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 33, 34);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_plus_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_plus_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_constant_plus_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_public_plus_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_private_plus_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_public_plus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_public_plus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_private_plus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_i32_private_plus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 33, 34);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_plus_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_plus_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_constant_plus_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_public_plus_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_private_plus_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_public_plus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_public_plus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_private_plus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_u64_private_plus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 65, 66);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_plus_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_plus_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_constant_plus_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_public_plus_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_private_plus_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_public_plus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_public_plus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_private_plus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_i64_private_plus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 65, 66);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_plus_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_plus_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_constant_plus_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_public_plus_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_private_plus_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_public_plus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_public_plus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_private_plus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_u128_private_plus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 129, 130);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_plus_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_plus_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_constant_plus_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_public_plus_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_private_plus_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_public_plus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_public_plus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_private_plus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_i128_private_plus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 129, 130);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_plus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_plus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_plus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_plus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_plus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_plus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_plus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_plus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_plus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 9, 10);
    }

    // Exhaustive tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_plus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_plus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_plus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_plus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_plus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_plus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_plus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_plus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 9, 10);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_plus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 9, 10);
    }
}
