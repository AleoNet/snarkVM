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

impl<E: Environment, I: IntegerType> Equal<Self> for Integer<E, I> {
    type Boolean = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    fn is_equal(&self, other: &Self) -> Self::Boolean {
        // Determine if this operation is constant or variable.
        match self.is_constant() && other.is_constant() {
            true => self
                .bits_le
                .iter()
                .zip_eq(other.bits_le.iter())
                .map(|(this, that)| this.is_equal(that))
                .fold(Boolean::constant(true), |a, b| a & b),
            false => {
                // Instead of comparing the bits of `self` and `other` directly, the integers are
                // converted into a field elements, and checked if they are equivalent as field elements.
                // Note: This is safe as the field is larger than the maximum integer type supported.
                self.to_field().is_equal(&other.to_field())
            }
        }
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Boolean {
        !self.is_equal(other)
    }
}

impl<E: Environment, I: IntegerType> Count<dyn Equal<Integer<E, I>, Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(input: &Self::Case) -> CircuitCount {
        match input.0.is_constant() && input.1.is_constant() {
            true => CircuitCount::exact(0, 0, 0, 0),
            false => CircuitCount::exact(0, 0, 2, 3),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Equal<Integer<E, I>, Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn output_mode(input: &Self::Case) -> Mode {
        match input.0.is_constant() && input.1.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::ops::RangeInclusive;

    const ITERATIONS: usize = 100;

    #[rustfmt::skip]
    fn check_equals<I: IntegerType>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let expected = first == second;
        let _case = format!("({} == {})", first, second);

        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.is_equal(&b);
            assert_eq!(expected, candidate.eject_value());
            assert_count!(Integer<Circuit, I>, Equal<Integer<Circuit, I>, Boolean=Boolean<Circuit>>, &(mode_a, mode_b));
            assert_output_mode!(candidate, Integer<Circuit, I>, Equal<Integer<Circuit, I>, Boolean=Boolean<Circuit>>, &(mode_a, mode_b));
        });


        // Commute the operation.
        let a = Integer::<Circuit, I>::new(mode_a, second);
        let b = Integer::<Circuit, I>::new(mode_b, first);
        Circuit::scope(name, || {
            let candidate = a.is_equal(&b);
            assert_eq!(expected, candidate.eject_value());
            assert_count!(Integer<Circuit, I>, Equal<Integer<Circuit, I>, Boolean=Boolean<Circuit>>, &(mode_a, mode_b));
            assert_output_mode!(candidate, Integer<Circuit, I>, Equal<Integer<Circuit, I>, Boolean=Boolean<Circuit>>, &(mode_a, mode_b));
        });
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Eq: {} == {} {}", mode_a, mode_b, i);
            check_equals(&name, first, second, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
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
                );
            }
        }
    }

    #[test]
    fn test_u8_constant_equals_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u8_constant_equals_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_equals_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_equals_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_equals_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_equals_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_equals_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_equals_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_equals_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_equals_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_equals_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_equals_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_equals_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_equals_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_equals_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_equals_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_equals_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_equals_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_equals_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u16_constant_equals_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_equals_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_equals_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_equals_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_equals_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_equals_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_equals_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_equals_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_equals_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i16_constant_equals_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_equals_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_equals_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_equals_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_equals_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_equals_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_equals_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_equals_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_equals_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u32_constant_equals_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_equals_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_equals_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_equals_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_equals_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_equals_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_equals_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_equals_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_equals_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i32_constant_equals_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_equals_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_equals_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_equals_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_equals_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_equals_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_equals_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_equals_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_equals_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u64_constant_equals_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_equals_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_equals_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_equals_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_equals_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_equals_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_equals_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_equals_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_equals_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i64_constant_equals_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_equals_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_equals_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_equals_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_equals_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_equals_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_equals_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_equals_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_equals_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u128_constant_equals_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_equals_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_equals_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_equals_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_equals_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_equals_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_equals_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_equals_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_equals_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i128_constant_equals_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_equals_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_equals_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_equals_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_equals_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_equals_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_equals_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_equals_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_equals_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_equals_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_equals_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_equals_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_equals_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_equals_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_equals_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_equals_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_equals_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_equals_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_equals_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_equals_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_equals_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_equals_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_equals_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_equals_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_equals_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_equals_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private);
    }
}
