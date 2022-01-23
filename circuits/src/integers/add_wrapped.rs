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
use crate::helpers::Adder;

use itertools::Itertools;

impl<E: Environment, I: IntegerType> AddWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_add(&other.eject_value()))
        } else {
            let mut bits_le = Vec::with_capacity(I::BITS);
            let mut carry = Boolean::new(Mode::Constant, false);

            // Perform a ripple-carry adder on the bits.
            for (index, (a, b)) in self
                .bits_le
                .iter()
                .zip_eq(other.bits_le.iter())
                .take(I::BITS)
                .enumerate()
            {
                match index != (I::BITS - 1) {
                    // For all bits up to the penultimate bit, perform a full-adder on `a` and `b`.
                    true => {
                        let (sum, next_carry) = a.adder(b, &carry);
                        bits_le.push(sum);
                        carry = next_carry;
                    }
                    // For the MSB, perform a full-adder excluding the carry update on `a` and `b`.
                    false => {
                        let sum = a.xor(b).xor(&carry);
                        bits_le.push(sum);
                    }
                };
            }

            // Stores the sum of `self` and `other` in `self`.
            Integer::from_bits(bits_le)
        }
    }
}

#[rustfmt::skip]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use num_traits::{One, Zero};
    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

    fn check_add_wrapped<I: IntegerType, IC: IntegerTrait<I>>(
        name: &str,
        expected: I,
        a: &IC,
        b: &IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let case = format!("({} + {})", a.eject_value(), b.eject_value());

            let candidate = a.add_wrapped(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            assert_eq!(num_constants, scope.num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, scope.num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, scope.num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, scope.num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    fn check_overflow<I: IntegerType, IC: IntegerTrait<I>>(
        first: I,
        second: I,
        expected: I,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = IC::new(mode_a, first);
        let b = IC::new(mode_b, second);

        let name = format!("Add: {} + {} ({})", first, second, expected);
        check_add_wrapped::<I, IC>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
    }

    fn run_test<I: IntegerType, IC: IntegerTrait<I>>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    )
        where Standard: Distribution<I>
    {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());
            let expected = first.wrapping_add(&second);

            let a = IC::new(mode_a, first);
            let b = IC::new(mode_b, second);

            let name = format!("Add: a + b {}", i);
            check_add_wrapped::<I, IC>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
        }

        match I::is_signed() {
            true => {
                check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
                check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            },
            false => {
                check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
                check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_plus_public() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Public, 1, 0, 19, 19);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Public, 1, 0, 13, 13);
    }

    #[test]
    fn test_u8_constant_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Private, 1, 0, 19, 19);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Private, 1, 0, 13, 13);
    }

    #[test]
    fn test_u8_public_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Public, Mode::Constant, 1, 0, 13, 13);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Public, Mode::Constant, 1, 0, 19, 19);
    }

    #[test]
    fn test_u8_private_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Private, Mode::Constant, 1, 0, 13, 13);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Private, Mode::Constant, 1, 0, 19, 19);
    }

    #[test]
    fn test_u8_public_plus_public() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_u8_public_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 34, 34);
    }

    #[test]
    fn test_u8_private_plus_public() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_u8_private_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 34, 34);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_plus_constant() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_plus_public() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Public, 1, 0, 19, 19);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Public, 1, 0, 13, 13);
    }

    #[test]
    fn test_i8_constant_plus_private() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Private, 1, 0, 19, 19);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Private, 1, 0, 13, 13);
    }

    #[test]
    fn test_i8_public_plus_constant() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Public, Mode::Constant, 1, 0, 13, 13);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Public, Mode::Constant, 1, 0, 19, 19);
    }

    #[test]
    fn test_i8_private_plus_constant() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Private, Mode::Constant, 1, 0, 13, 13);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Private, Mode::Constant, 1, 0, 19, 19);
    }

    #[test]
    fn test_i8_public_plus_public() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_i8_public_plus_private() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 34, 34);
    }

    #[test]
    fn test_i8_private_plus_public() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_i8_private_plus_private() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 34, 34);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_plus_constant() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_plus_public() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Public, 1, 0, 43, 43);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Public, 1, 0, 29, 29);
    }

    #[test]
    fn test_u16_constant_plus_private() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Private, 1, 0, 43, 43);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Private, 1, 0, 29, 29);
    }

    #[test]
    fn test_u16_public_plus_constant() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Public, Mode::Constant, 1, 0, 29, 29);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Public, Mode::Constant, 1, 0, 43, 43);
    }

    #[test]
    fn test_u16_private_plus_constant() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Private, Mode::Constant, 1, 0, 29, 29);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Private, Mode::Constant, 1, 0, 43, 43);
    }

    #[test]
    fn test_u16_public_plus_public() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_u16_public_plus_private() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 74, 74);
    }

    #[test]
    fn test_u16_private_plus_public() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_u16_private_plus_private() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 74, 74);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_plus_constant() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_plus_public() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Public, 1, 0, 43, 43);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Public, 1, 0, 29, 29);
    }

    #[test]
    fn test_i16_constant_plus_private() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Private, 1, 0, 43, 43);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Private, 1, 0, 29, 29);
    }

    #[test]
    fn test_i16_public_plus_constant() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Public, Mode::Constant, 1, 0, 29, 29);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Public, Mode::Constant, 1, 0, 43, 43);
    }

    #[test]
    fn test_i16_private_plus_constant() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Private, Mode::Constant, 1, 0, 29, 29);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Private, Mode::Constant, 1, 0, 43, 43);
    }

    #[test]
    fn test_i16_public_plus_public() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_i16_public_plus_private() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 74, 74);
    }

    #[test]
    fn test_i16_private_plus_public() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_i16_private_plus_private() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 74, 74);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_plus_constant() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_plus_public() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Public, 1, 0, 91, 91);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Public, 1, 0, 61, 61);
    }

    #[test]
    fn test_u32_constant_plus_private() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Private, 1, 0, 91, 91);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Private, 1, 0, 61, 61);
    }

    #[test]
    fn test_u32_public_plus_constant() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Public, Mode::Constant, 1, 0, 61, 61);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Public, Mode::Constant, 1, 0, 91, 91);
    }

    #[test]
    fn test_u32_private_plus_constant() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Private, Mode::Constant, 1, 0, 61, 61);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Private, Mode::Constant, 1, 0, 91, 91);
    }

    #[test]
    fn test_u32_public_plus_public() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_u32_public_plus_private() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 154, 154);
    }

    #[test]
    fn test_u32_private_plus_public() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_u32_private_plus_private() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 154, 154);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_plus_constant() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_plus_public() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Public, 1, 0, 91, 91);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Public, 1, 0, 61, 61);
    }

    #[test]
    fn test_i32_constant_plus_private() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Private, 1, 0, 91, 91);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Private, 1, 0, 61, 61);
    }

    #[test]
    fn test_i32_public_plus_constant() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Public, Mode::Constant, 1, 0, 61, 61);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Public, Mode::Constant, 1, 0, 91, 91);
    }

    #[test]
    fn test_i32_private_plus_constant() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Private, Mode::Constant, 1, 0, 61, 61);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Private, Mode::Constant, 1, 0, 91, 91);
    }

    #[test]
    fn test_i32_public_plus_public() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_i32_public_plus_private() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 154, 154);
    }

    #[test]
    fn test_i32_private_plus_public() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_i32_private_plus_private() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 154, 154);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_plus_constant() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_plus_public() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Public, 1, 0, 187, 187);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Public, 1, 0, 125, 125);
    }

    #[test]
    fn test_u64_constant_plus_private() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Private, 1, 0, 187, 187);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Private, 1, 0, 125, 125);
    }

    #[test]
    fn test_u64_public_plus_constant() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Public, Mode::Constant, 1, 0, 125, 125);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Public, Mode::Constant, 1, 0, 187, 187);
    }

    #[test]
    fn test_u64_private_plus_constant() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Private, Mode::Constant, 1, 0, 125, 125);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Private, Mode::Constant, 1, 0, 187, 187);
    }

    #[test]
    fn test_u64_public_plus_public() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_u64_public_plus_private() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 314, 314);
    }

    #[test]
    fn test_u64_private_plus_public() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_u64_private_plus_private() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 314, 314);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_plus_constant() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_plus_public() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Public, 1, 0, 187, 187);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Public, 1, 0, 125, 125);
    }

    #[test]
    fn test_i64_constant_plus_private() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Private, 1, 0, 187, 187);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Private, 1, 0, 125, 125);
    }

    #[test]
    fn test_i64_public_plus_constant() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Public, Mode::Constant, 1, 0, 125, 125);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Public, Mode::Constant, 1, 0, 187, 187);
    }

    #[test]
    fn test_i64_private_plus_constant() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Private, Mode::Constant, 1, 0, 125, 125);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Private, Mode::Constant, 1, 0, 187, 187);
    }

    #[test]
    fn test_i64_public_plus_public() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_i64_public_plus_private() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 314, 314);
    }

    #[test]
    fn test_i64_private_plus_public() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_i64_private_plus_private() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 314, 314);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_plus_constant() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_plus_public() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Public, 1, 0, 379, 379);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Public, 1, 0, 253, 253);
    }

    #[test]
    fn test_u128_constant_plus_private() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Constant, Mode::Private, 1, 0, 379, 379);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Constant, Mode::Private, 1, 0, 253, 253);
    }

    #[test]
    fn test_u128_public_plus_constant() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Public, Mode::Constant, 1, 0, 253, 253);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Public, Mode::Constant, 1, 0, 379, 379);
    }

    #[test]
    fn test_u128_private_plus_constant() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::zero(), Mode::Private, Mode::Constant, 1, 0, 253, 253);
        check_overflow::<I, IC>(I::one(), I::MAX, I::zero(), Mode::Private, Mode::Constant, 1, 0, 379, 379);
    }

    #[test]
    fn test_u128_public_plus_public() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_u128_public_plus_private() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 634, 634);
    }

    #[test]
    fn test_u128_private_plus_public() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_u128_private_plus_private() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 634, 634);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_plus_constant() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_plus_public() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Public, 1, 0, 379, 379);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Public, 1, 0, 253, 253);
    }

    #[test]
    fn test_i128_constant_plus_private() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Constant, Mode::Private, 1, 0, 379, 379);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Constant, Mode::Private, 1, 0, 253, 253);
    }

    #[test]
    fn test_i128_public_plus_constant() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Public, Mode::Constant, 1, 0, 253, 253);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Public, Mode::Constant, 1, 0, 379, 379);
    }

    #[test]
    fn test_i128_private_plus_constant() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow::<I, IC>(I::MAX, I::one(), I::MIN, Mode::Private, Mode::Constant, 1, 0, 253, 253);
        check_overflow::<I, IC>(I::one(), I::MAX, I::MIN, Mode::Private, Mode::Constant, 1, 0, 379, 379);
    }

    #[test]
    fn test_i128_public_plus_public() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_i128_public_plus_private() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 634, 634);
    }

    #[test]
    fn test_i128_private_plus_public() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_i128_private_plus_private() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 634, 634);
    }
}
