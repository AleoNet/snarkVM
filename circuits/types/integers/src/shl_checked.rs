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

impl<E: Environment, I: IntegerType, M: Magnitude> Shl<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    fn shl(self, rhs: Integer<E, M>) -> Self::Output {
        self << &rhs
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Shl<Integer<E, M>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn shl(self, rhs: Integer<E, M>) -> Self::Output {
        self << &rhs
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Shl<&Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    fn shl(self, rhs: &Integer<E, M>) -> Self::Output {
        &self << rhs
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Shl<&Integer<E, M>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn shl(self, rhs: &Integer<E, M>) -> Self::Output {
        let mut output = self.clone();
        output <<= rhs;
        output
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> ShlAssign<Integer<E, M>> for Integer<E, I> {
    fn shl_assign(&mut self, rhs: Integer<E, M>) {
        *self <<= &rhs
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> ShlAssign<&Integer<E, M>> for Integer<E, I> {
    fn shl_assign(&mut self, rhs: &Integer<E, M>) {
        // Stores the result of `self` << `other` in `self`.
        *self = self.shl_checked(rhs);
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> ShlChecked<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn shl_checked(&self, rhs: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && rhs.is_constant() {
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            match self.eject_value().checked_shl(rhs.eject_value().to_u32().unwrap()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Constant shifted by constant exceeds the allowed bitwidth."),
            }
        } else {
            // Index of the first upper bit of rhs that must be zero.
            // This is a safe case as I::BITS = 8, 16, 32, 64, or 128.
            // Therefore there is at least one trailing zero.
            let first_upper_bit_index = I::BITS.trailing_zeros() as usize;

            let upper_bits_are_nonzero =
                rhs.bits_le[first_upper_bit_index..].iter().fold(Boolean::constant(false), |a, b| a | b);

            // Halt if upper bits of rhs are constant and nonzero.
            if upper_bits_are_nonzero.is_constant() && upper_bits_are_nonzero.eject_value() {
                E::halt("Integer shifted by constant exceeds the allowed bitwidth.")
            }
            // Enforce that the appropriate number of upper bits in rhs are zero.
            E::assert_eq(upper_bits_are_nonzero, E::zero());

            // Perform a wrapping shift left.
            self.shl_wrapped(rhs)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 32;

    #[rustfmt::skip]
    fn check_shl<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} << {})", a.eject_value(), b.eject_value());

        match first.checked_shl(second.to_u32().unwrap()) {
            Some(value) => {
                check_operation_passes(name, &case, value, &a, &b, Integer::shl_checked, num_constants, num_public, num_private, num_constraints);
            }
            None => match (mode_a, mode_b) {
                (_, Mode::Constant) => check_operation_halts(&a, &b, Integer::shl_checked),
                _ => check_operation_fails(name, &case, &a, &b, Integer::shl_checked, num_constants, num_public, num_private, num_constraints),
            },
        };
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_shl = |name: &str, first: I, second: M| check_shl(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: M = UniformRand::rand(&mut test_rng());

            let name = format!("Shl: {} << {} {}", mode_a, mode_b, i);
            check_shl(&name, first, second);

            // Check that shift left by one is computed correctly.
            let name = format!("Double: {} << {} {}", mode_a, mode_b, i);
            check_shl(&name, first, M::one());

            // Check that shift left by two is computed correctly.
            let name = format!("Quadruple: {} << {} {}", mode_a, mode_b, i);
            check_shl(&name, first, M::one() + M::one());
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item=I>,
        RangeInclusive<M>: Iterator<Item=M>
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Shl: ({} << {})", first, second);
                check_shl(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    // Tests for u8, where shift magnitude is u8

    #[test]
    fn test_u8_constant_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 32, 35);
    }

    #[test]
    fn test_u8_constant_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 32, 35);
    }

    #[test]
    fn test_u8_public_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    fn test_u8_public_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 33, 36);
    }

    #[test]
    fn test_u8_private_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    fn test_u8_private_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 33, 36);
    }

    // Tests for i8, where shift magnitude is u8

    #[test]
    fn test_i8_constant_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 32, 35);
    }

    #[test]
    fn test_i8_constant_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 32, 35);
    }

    #[test]
    fn test_i8_public_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    fn test_i8_public_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 33, 36);
    }

    #[test]
    fn test_i8_private_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    fn test_i8_private_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 33, 36);
    }

    // Tests for u16, where shift magnitude is u8

    #[test]
    fn test_u16_constant_shl_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 57, 60);
    }

    #[test]
    fn test_u16_constant_shl_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 57, 60);
    }

    #[test]
    fn test_u16_public_shl_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shl_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 58, 61);
    }

    #[test]
    fn test_u16_public_shl_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 58, 61);
    }

    #[test]
    fn test_u16_private_shl_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 58, 61);
    }

    #[test]
    fn test_u16_private_shl_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 58, 61);
    }

    // Tests for i16, where shift magnitude is u8

    #[test]
    fn test_i16_constant_shl_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 57, 60);
    }

    #[test]
    fn test_i16_constant_shl_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 57, 60);
    }

    #[test]
    fn test_i16_public_shl_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shl_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 58, 61);
    }

    #[test]
    fn test_i16_public_shl_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 58, 61);
    }

    #[test]
    fn test_i16_private_shl_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 58, 61);
    }

    #[test]
    fn test_i16_private_shl_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 58, 61);
    }

    // Tests for u32, where shift magnitude is u8

    #[test]
    fn test_u32_constant_shl_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 106, 109);
    }

    #[test]
    fn test_u32_constant_shl_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 106, 109);
    }

    #[test]
    fn test_u32_public_shl_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shl_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 107, 110);
    }

    #[test]
    fn test_u32_public_shl_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 107, 110);
    }

    #[test]
    fn test_u32_private_shl_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 107, 110);
    }

    #[test]
    fn test_u32_private_shl_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 107, 110);
    }

    // Tests for i32, where shift magnitude is u8

    #[test]
    fn test_i32_constant_shl_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 106, 109);
    }

    #[test]
    fn test_i32_constant_shl_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 106, 109);
    }

    #[test]
    fn test_i32_public_shl_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shl_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 107, 110);
    }

    #[test]
    fn test_i32_public_shl_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 107, 110);
    }

    #[test]
    fn test_i32_private_shl_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 107, 110);
    }

    #[test]
    fn test_i32_private_shl_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 107, 110);
    }

    // Tests for u64, where shift magnitude is u8

    #[test]
    fn test_u64_constant_shl_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 203, 206);
    }

    #[test]
    fn test_u64_constant_shl_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 203, 206);
    }

    #[test]
    fn test_u64_public_shl_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shl_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 204, 207);
    }

    #[test]
    fn test_u64_public_shl_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 204, 207);
    }

    #[test]
    fn test_u64_private_shl_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 204, 207);
    }

    #[test]
    fn test_u64_private_shl_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 204, 207);
    }

    // Tests for i64, where shift magnitude is u8

    #[test]
    fn test_i64_constant_shl_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 203, 206);
    }

    #[test]
    fn test_i64_constant_shl_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 203, 206);
    }

    #[test]
    fn test_i64_public_shl_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shl_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 204, 207);
    }

    #[test]
    fn test_i64_public_shl_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 204, 207);
    }

    #[test]
    fn test_i64_private_shl_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 204, 207);
    }

    #[test]
    fn test_i64_private_shl_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 204, 207);
    }

    // Tests for u128, where shift magnitude is u8

    #[test]
    fn test_u128_constant_shl_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 333, 336);
    }

    #[test]
    fn test_u128_constant_shl_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 333, 336);
    }

    #[test]
    fn test_u128_public_shl_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shl_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 336, 339);
    }

    #[test]
    fn test_u128_public_shl_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 336, 339);
    }

    #[test]
    fn test_u128_private_shl_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 336, 339);
    }

    #[test]
    fn test_u128_private_shl_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 336, 339);
    }

    // Tests for i128, where shift magnitude is u8

    #[test]
    fn test_i128_constant_shl_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 333, 336);
    }

    #[test]
    fn test_i128_constant_shl_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 333, 336);
    }

    #[test]
    fn test_i128_public_shl_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shl_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 336, 339);
    }

    #[test]
    fn test_i128_public_shl_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 336, 339);
    }

    #[test]
    fn test_i128_private_shl_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 336, 339);
    }

    #[test]
    fn test_i128_private_shl_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 336, 339);
    }

    // Tests for u8, where shift magnitude is u16

    #[test]
    fn test_u8_constant_shl_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 40, 43);
    }

    #[test]
    fn test_u8_constant_shl_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 40, 43);
    }

    #[test]
    fn test_u8_public_shl_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shl_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 41, 44);
    }

    #[test]
    fn test_u8_public_shl_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 41, 44);
    }

    #[test]
    fn test_u8_private_shl_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 41, 44);
    }

    #[test]
    fn test_u8_private_shl_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 41, 44);
    }

    // Tests for i8, where shift magnitude is u16

    #[test]
    fn test_i8_constant_shl_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 40, 43);
    }

    #[test]
    fn test_i8_constant_shl_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 40, 43);
    }

    #[test]
    fn test_i8_public_shl_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shl_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 41, 44);
    }

    #[test]
    fn test_i8_public_shl_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 41, 44);
    }

    #[test]
    fn test_i8_private_shl_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 41, 44);
    }

    #[test]
    fn test_i8_private_shl_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 41, 44);
    }

    // Tests for u16, where shift magnitude is u16

    #[test]
    fn test_u16_constant_shl_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 65, 68);
    }

    #[test]
    fn test_u16_constant_shl_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 65, 68);
    }

    #[test]
    fn test_u16_public_shl_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shl_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 66, 69);
    }

    #[test]
    fn test_u16_public_shl_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 66, 69);
    }

    #[test]
    fn test_u16_private_shl_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 66, 69);
    }

    #[test]
    fn test_u16_private_shl_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 66, 69);
    }

    // Tests for i16, where shift magnitude is u16

    #[test]
    fn test_i16_constant_shl_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 65, 68);
    }

    #[test]
    fn test_i16_constant_shl_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 65, 68);
    }

    #[test]
    fn test_i16_public_shl_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shl_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 66, 69);
    }

    #[test]
    fn test_i16_public_shl_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 66, 69);
    }

    #[test]
    fn test_i16_private_shl_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 66, 69);
    }

    #[test]
    fn test_i16_private_shl_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 66, 69);
    }

    // Tests for u32, where shift magnitude is u16

    #[test]
    fn test_u32_constant_shl_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 114, 117);
    }

    #[test]
    fn test_u32_constant_shl_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 114, 117);
    }

    #[test]
    fn test_u32_public_shl_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shl_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 115, 118);
    }

    #[test]
    fn test_u32_public_shl_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 115, 118);
    }

    #[test]
    fn test_u32_private_shl_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 115, 118);
    }

    #[test]
    fn test_u32_private_shl_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 115, 118);
    }

    // Tests for i32, where shift magnitude is u16

    #[test]
    fn test_i32_constant_shl_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 114, 117);
    }

    #[test]
    fn test_i32_constant_shl_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 114, 117);
    }

    #[test]
    fn test_i32_public_shl_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shl_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 115, 118);
    }

    #[test]
    fn test_i32_public_shl_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 115, 118);
    }

    #[test]
    fn test_i32_private_shl_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 115, 118);
    }

    #[test]
    fn test_i32_private_shl_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 115, 118);
    }

    // Tests for u64, where shift magnitude is u16

    #[test]
    fn test_u64_constant_shl_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 211, 214);
    }

    #[test]
    fn test_u64_constant_shl_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 211, 214);
    }

    #[test]
    fn test_u64_public_shl_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shl_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 212, 215);
    }

    #[test]
    fn test_u64_public_shl_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 212, 215);
    }

    #[test]
    fn test_u64_private_shl_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 212, 215);
    }

    #[test]
    fn test_u64_private_shl_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 212, 215);
    }

    // Tests for i64, where shift magnitude is u16

    #[test]
    fn test_i64_constant_shl_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 211, 214);
    }

    #[test]
    fn test_i64_constant_shl_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 211, 214);
    }

    #[test]
    fn test_i64_public_shl_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shl_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 212, 215);
    }

    #[test]
    fn test_i64_public_shl_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 212, 215);
    }

    #[test]
    fn test_i64_private_shl_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 212, 215);
    }

    #[test]
    fn test_i64_private_shl_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 212, 215);
    }

    // Tests for u128, where shift magnitude is u16

    #[test]
    fn test_u128_constant_shl_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 341, 344);
    }

    #[test]
    fn test_u128_constant_shl_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 341, 344);
    }

    #[test]
    fn test_u128_public_shl_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shl_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 344, 347);
    }

    #[test]
    fn test_u128_public_shl_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 344, 347);
    }

    #[test]
    fn test_u128_private_shl_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 344, 347);
    }

    #[test]
    fn test_u128_private_shl_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 344, 347);
    }

    // Tests for i128, where shift magnitude is u16

    #[test]
    fn test_i128_constant_shl_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 341, 344);
    }

    #[test]
    fn test_i128_constant_shl_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 341, 344);
    }

    #[test]
    fn test_i128_public_shl_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shl_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 344, 347);
    }

    #[test]
    fn test_i128_public_shl_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 344, 347);
    }

    #[test]
    fn test_i128_private_shl_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 344, 347);
    }

    #[test]
    fn test_i128_private_shl_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 344, 347);
    }

    // Tests for u8, where shift magnitude is u32

    #[test]
    fn test_u8_constant_shl_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 56, 59);
    }

    #[test]
    fn test_u8_constant_shl_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 56, 59);
    }

    #[test]
    fn test_u8_public_shl_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shl_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 57, 60);
    }

    #[test]
    fn test_u8_public_shl_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 57, 60);
    }

    #[test]
    fn test_u8_private_shl_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 57, 60);
    }

    #[test]
    fn test_u8_private_shl_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 57, 60);
    }

    // Tests for i8, where shift magnitude is u32

    #[test]
    fn test_i8_constant_shl_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 56, 59);
    }

    #[test]
    fn test_i8_constant_shl_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 56, 59);
    }

    #[test]
    fn test_i8_public_shl_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shl_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 57, 60);
    }

    #[test]
    fn test_i8_public_shl_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 57, 60);
    }

    #[test]
    fn test_i8_private_shl_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 57, 60);
    }

    #[test]
    fn test_i8_private_shl_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 57, 60);
    }

    // Tests for u16, where shift magnitude is u32

    #[test]
    fn test_u16_constant_shl_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 81, 84);
    }

    #[test]
    fn test_u16_constant_shl_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 81, 84);
    }

    #[test]
    fn test_u16_public_shl_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shl_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 82, 85);
    }

    #[test]
    fn test_u16_public_shl_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 82, 85);
    }

    #[test]
    fn test_u16_private_shl_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 82, 85);
    }

    #[test]
    fn test_u16_private_shl_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 82, 85);
    }

    // Tests for i16, where shift magnitude is u32

    #[test]
    fn test_i16_constant_shl_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 81, 84);
    }

    #[test]
    fn test_i16_constant_shl_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 81, 84);
    }

    #[test]
    fn test_i16_public_shl_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shl_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 82, 85);
    }

    #[test]
    fn test_i16_public_shl_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 82, 85);
    }

    #[test]
    fn test_i16_private_shl_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 82, 85);
    }

    #[test]
    fn test_i16_private_shl_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 82, 85);
    }

    // Tests for u32, where shift magnitude is u32

    #[test]
    fn test_u32_constant_shl_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 130, 133);
    }

    #[test]
    fn test_u32_constant_shl_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 130, 133);
    }

    #[test]
    fn test_u32_public_shl_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shl_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 131, 134);
    }

    #[test]
    fn test_u32_public_shl_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 131, 134);
    }

    #[test]
    fn test_u32_private_shl_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 131, 134);
    }

    #[test]
    fn test_u32_private_shl_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 131, 134);
    }

    // Tests for i32, where shift magnitude is u32

    #[test]
    fn test_i32_constant_shl_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 130, 133);
    }

    #[test]
    fn test_i32_constant_shl_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 130, 133);
    }

    #[test]
    fn test_i32_public_shl_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shl_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 131, 134);
    }

    #[test]
    fn test_i32_public_shl_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 131, 134);
    }

    #[test]
    fn test_i32_private_shl_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 131, 134);
    }

    #[test]
    fn test_i32_private_shl_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 131, 134);
    }

    // Tests for u64, where shift magnitude is u32

    #[test]
    fn test_u64_constant_shl_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 227, 230);
    }

    #[test]
    fn test_u64_constant_shl_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 227, 230);
    }

    #[test]
    fn test_u64_public_shl_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shl_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 228, 231);
    }

    #[test]
    fn test_u64_public_shl_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 228, 231);
    }

    #[test]
    fn test_u64_private_shl_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 228, 231);
    }

    #[test]
    fn test_u64_private_shl_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 228, 231);
    }

    // Tests for i64, where shift magnitude is u32

    #[test]
    fn test_i64_constant_shl_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 227, 230);
    }

    #[test]
    fn test_i64_constant_shl_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 227, 230);
    }

    #[test]
    fn test_i64_public_shl_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shl_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 228, 231);
    }

    #[test]
    fn test_i64_public_shl_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 228, 231);
    }

    #[test]
    fn test_i64_private_shl_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 228, 231);
    }

    #[test]
    fn test_i64_private_shl_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 228, 231);
    }

    // Tests for u128, where shift magnitude is u32

    #[test]
    fn test_u128_constant_shl_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 357, 360);
    }

    #[test]
    fn test_u128_constant_shl_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 357, 360);
    }

    #[test]
    fn test_u128_public_shl_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shl_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 360, 363);
    }

    #[test]
    fn test_u128_public_shl_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 360, 363);
    }

    #[test]
    fn test_u128_private_shl_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 360, 363);
    }

    #[test]
    fn test_u128_private_shl_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 360, 363);
    }

    // Tests for i128, where shift magnitude is u32

    #[test]
    fn test_i128_constant_shl_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 357, 360);
    }

    #[test]
    fn test_i128_constant_shl_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 357, 360);
    }

    #[test]
    fn test_i128_public_shl_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shl_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 360, 363);
    }

    #[test]
    fn test_i128_public_shl_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 360, 363);
    }

    #[test]
    fn test_i128_private_shl_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 360, 363);
    }

    #[test]
    fn test_i128_private_shl_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 360, 363);
    }

    // Exhaustive tests for u8, where shift magnitude is u8

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 32, 35);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 32, 35);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 33, 36);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 33, 36);
    }

    // Tests for i8, where shift magnitude is u8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 32, 35);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 32, 35);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 33, 36);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 33, 36);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 33, 36);
    }
}
