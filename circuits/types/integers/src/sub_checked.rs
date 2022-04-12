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

impl<E: Environment, I: IntegerType> Sub<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment, I: IntegerType> Sub<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn sub(self, other: Integer<E, I>) -> Self::Output {
        self - &other
    }
}

impl<E: Environment, I: IntegerType> Sub<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        &self - other
    }
}

impl<E: Environment, I: IntegerType> Sub<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn sub(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output -= other;
        output
    }
}

impl<E: Environment, I: IntegerType> SubAssign<Integer<E, I>> for Integer<E, I> {
    fn sub_assign(&mut self, other: Integer<E, I>) {
        *self -= &other;
    }
}

impl<E: Environment, I: IntegerType> SubAssign<&Integer<E, I>> for Integer<E, I> {
    fn sub_assign(&mut self, other: &Integer<E, I>) {
        // Stores the difference of `self` and `other` in `self`.
        *self = self.sub_checked(other);
    }
}

impl<E: Environment, I: IntegerType> SubChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn sub_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the difference and return the new constant.
            match self.eject_value().checked_sub(&other.eject_value()) {
                Some(value) => Integer::constant(value),
                None => E::halt("Integer underflow on subtraction of two constants"),
            }
        } else {
            // Instead of subtracting the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and subtracted, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let difference = self.to_field() + (!other).to_field() + Field::one();

            // Extract the integer bits from the field element, with a carry bit.
            let (difference, carry) = match difference.to_lower_bits_le(I::BITS + 1).split_last() {
                Some((carry, bits_le)) => (Integer::from_bits_le(bits_le), carry.clone()),
                None => E::halt("Malformed difference detected during integer subtraction"),
            };

            // Check for underflow.
            match I::is_signed() {
                // For signed subtraction, overflow and underflow conditions are:
                //   - a > 0 && b < 0 && a - b > 0 (Overflow)
                //   - a < 0 && b > 0 && a - b < 0 (Underflow)
                //   - Note: if sign(a) == sign(b) then over/underflow is impossible.
                //   - Note: the result of an overflow and underflow must be negative and positive, respectively.
                true => {
                    let is_different_signs = self.msb().is_not_equal(other.msb());
                    let is_underflow = is_different_signs & difference.msb().is_equal(other.msb());
                    E::assert_eq(is_underflow, E::zero());
                }
                // For unsigned subtraction, ensure the carry bit is one.
                false => E::assert_eq(carry, E::one()),
            }

            // Return the difference of `self` and `other`.
            difference
        }
    }
}

impl<E: Environment, I: IntegerType> CountForOp<dyn SubChecked<Integer<E, I>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn count(input: &Self::Case) -> Count {
        match I::is_signed() {
            false => match (input.0, input.1) {
                (Mode::Constant, Mode::Constant) => Count::exact(I::BITS, 0, 0, 0),
                (_, _) => Count::exact(0, 0, I::BITS + 1, I::BITS + 3),
            },
            true => match (input.0, input.1) {
                (Mode::Constant, Mode::Constant) => Count::exact(I::BITS, 0, 0, 0),
                (Mode::Constant, _) => Count::exact(0, 0, I::BITS + 3, I::BITS + 5),
                (_, Mode::Constant) => Count::exact(0, 0, I::BITS + 2, I::BITS + 4),
                (_, _) => Count::exact(0, 0, I::BITS + 4, I::BITS + 6),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputModeForOp<dyn SubChecked<Integer<E, I>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn output_mode(input: &Self::Case) -> Mode {
        match (input.0, input.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

impl<E: Environment, I: IntegerType> MetadataForOp<dyn SubChecked<Integer<E, I>, Output = Integer<E, I>>>
    for Integer<E, I>
{
}

impl<E: Environment, I: IntegerType> CountForOp<dyn Sub<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(input: &Self::Case) -> Count {
        <Self as CountForOp<dyn SubChecked<Integer<E, I>, Output = Integer<E, I>>>>::count(input)
    }
}

impl<E: Environment, I: IntegerType> OutputModeForOp<dyn Sub<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn output_mode(input: &Self::Case) -> Mode {
        <Self as OutputModeForOp<dyn SubChecked<Integer<E, I>, Output = Integer<E, I>>>>::output_mode(input)
    }
}

impl<E: Environment, I: IntegerType> MetadataForOp<dyn Sub<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_sub<I: IntegerType + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let case = format!("({} - {})", a.eject_value(), b.eject_value());
        match first.checked_sub(&second) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.sub_checked(&b);
                assert_eq!(expected, candidate.eject_value());
                assert_count!(Integer<Circuit, I>, Sub<Integer<Circuit, I>, Output=Integer<Circuit, I>>, &(mode_a, mode_b));
                assert_output_mode!(candidate, Integer<Circuit, I>, Sub<Integer<Circuit, I>, Output=Integer<Circuit, I>>, &(mode_a, mode_b));
            }),
            None => match mode_a.is_constant() && mode_b.is_constant() {
                true => check_operation_halts(&a, &b, Integer::sub_checked),
                false => Circuit::scope(name, || {
                    let candidate = a.sub_checked(&b);
                    assert_count_fails!(Integer<Circuit, I>, Sub<Integer<Circuit, I>, Output=Integer<Circuit, I>>, &(mode_a, mode_b));
                }),
            },
        }
        Circuit::reset();
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let check_sub = | name: &str, first: I, second: I | check_sub(name, first, second, mode_a, mode_b);

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, first, second);
        }

        // Overflow
        if I::is_signed() {
            check_sub("MAX - (-1)", I::MAX, I::zero() - I::one());
        }
        // Underflow
        check_sub("MIN - 1", I::MIN, I::one());
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Sub: ({} - {})", first, second);
                check_sub(&name, first, second, mode_a, mode_b);
            }
        }
    }

    // Tests for u8.

    #[test]
    fn test_u8_constant_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u8_constant_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u16_constant_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i16_constant_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u32_constant_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i32_constant_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u64_constant_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i64_constant_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u128_constant_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i128_constant_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_public_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_minus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_minus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_minus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_minus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_minus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_minus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_minus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_minus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_minus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_minus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_minus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_minus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_minus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_minus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_minus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_minus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_minus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_minus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private);
    }
}
