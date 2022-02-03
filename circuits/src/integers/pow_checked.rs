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

impl<E: Environment, I: IntegerType, M: private::Magnitude> PowChecked<M> for Integer<E, I> {
    type Exponent = Integer<E, M>;
    type Output = Self;

    #[inline]
    fn pow_checked(&self, other: &Self::Exponent) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            match self.eject_value().checked_pow(other.eject_value().to_u32().unwrap()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on exponentiation of two constants"),
            }
        } else {
            let mut result = Self::one();

            // TODO (@pranav) In each step, we check that we have not overflowed,
            //  yet we know that in the first step, we do not need to check and
            //  in general we do not need to check for overflow until we have found
            //  the second bit that has been set. Optimize.
            for bit in other.bits_le.iter().rev() {
                result = (&result).mul_checked(&result);
                // TODO (@pranav) We explicitly inline the implementation for mul_checked
                //  since we only want to check for overflow if the bit of the exponent is set.
                //  Dedup this code.
                let result_times_self = if I::is_signed() {
                    // This is safe since I::BITS is always greater than 0.
                    let result_msb = result.bits_le.last().unwrap();
                    let self_msb = self.bits_le.last().unwrap();

                    // Multiply the absolute value of `self` and `other` in the base field.
                    let result_absolute_value = Self::ternary(result_msb, &(!&result).add_wrapped(&Self::one()), &result);
                    let self_absolute_value = Self::ternary(self_msb, &(!self).add_wrapped(&Self::one()), self);
                    let mut bits_le =
                        Self::multiply_bits_in_field(&result_absolute_value.bits_le, &self_absolute_value.bits_le, true);

                    let bits_are_nonzero = |bits: &[Boolean<E>]| {
                        bits.iter().fold(Boolean::new(Mode::Constant, false), |bit, at_least_one_is_set| {
                            bit.or(at_least_one_is_set)
                        })
                    };

                    // We need to check that the abs(a) * abs(b) did not exceed the unsigned maximum.
                    let carry_bits_nonzero = bits_are_nonzero(&bits_le[I::BITS..]);

                    let product_msb = &bits_le[I::BITS - 1];
                    let operands_same_sign = &result_msb.is_eq(self_msb);

                    // If the product should be positive, then it cannot exceed the signed maximum.
                    let positive_product_overflows = operands_same_sign.and(&product_msb);

                    // If the product should be negative, then it cannot exceed the absolute value of the signed minimum.
                    let lower_product_bits_nonzero = &bits_are_nonzero(&bits_le[..(I::BITS - 1)]);
                    let negative_product_lt_or_eq_signed_min =
                        (!product_msb).or(&product_msb.and(&!lower_product_bits_nonzero));
                    let negative_product_underflows = (!operands_same_sign).and(&!negative_product_lt_or_eq_signed_min);

                    let overflow = carry_bits_nonzero.or(&positive_product_overflows).or(&negative_product_underflows);

                    E::assert_eq(overflow.and(&bit), E::zero());

                    // Remove carry bits.
                    bits_le.truncate(I::BITS);

                    let value = Integer { bits_le, phantom: Default::default() };

                    // Return the product of `self` and `other` with the appropriate sign.
                    Self::ternary(operands_same_sign, &value, &(!&value).add_wrapped(&Self::one()))
                } else {
                    let mut bits_le = Self::multiply_bits_in_field(&self.bits_le, &other.bits_le, true);

                    // For unsigned multiplication, check that the none of the carry bits are set.
                    let overflow = bits_le[I::BITS..]
                        .iter()
                        .fold(Boolean::new(Mode::Constant, false), |bit, at_least_one_is_set| {
                            bit.or(at_least_one_is_set)
                        });
                    E::assert_eq(overflow.and(&bit), E::zero());

                    // Remove carry bits.
                    bits_le.truncate(I::BITS);

                    // Return the product of `self` and `other`.
                    Integer { bits_le, phantom: Default::default() }
                };

                result = Self::ternary(&bit, &result_times_self, &result);
            }
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    // Lowered to 32, since we run (~5 * ITERATIONS) cases for most tests.
    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_pow_checked<I: IntegerType, M: private::Magnitude>(
        name: &str,
        expected: I,
        a: &Integer<Circuit, I>,
        b: &Integer<Circuit, M>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let case = format!("({} ** {})", a.eject_value(), b.eject_value());

            let candidate = a.pow_checked(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());

            // assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            // assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            // assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            // assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset()
    }

    #[rustfmt::skip]
    fn check_pow_halts<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: M,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.pow_checked(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_pow_fails<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: M,
    ) {
        let name = format!("Pow: {} ** {} overflows", value_a, value_b);
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        Circuit::scoped(&name, || {
            let case = format!("({} ** {})", a.eject_value(), b.eject_value());
            let _candidate = a.pow_checked(&b);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    #[rustfmt::skip]
    fn run_overflow_and_corner_case_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let check_pow_without_expected_parameters = |first: I, second: M, expected: I | {
            Circuit::scoped("Pow(No Expected Parameters)", || {
                let a = Integer::<Circuit, I>::new(mode_a, first);
                let b = Integer::<Circuit, M>::new(mode_b, second);

                let case = format!("({} ** {})", a.eject_value(), b.eject_value());
                let candidate = a.pow_checked(&b);
                assert_eq!(
                    expected,
                    candidate.eject_value(),
                    "{} != {} := {}",
                    expected,
                    candidate.eject_value(),
                    case
                );
                assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
            });
            Circuit::reset()
        };

        let check_pow_overflows = | first: I, second: M | {
            match (mode_a, mode_b) {
                (Mode::Constant, Mode::Constant) => check_pow_halts::<I, M>(mode_a, mode_b, first, second),
                _ => check_pow_fails::<I, M>(mode_a, mode_b, first, second)
            }
        };

        // Test operation without checking for the expected number of
        // constants, public variables, private variables, and constraints.
        for _i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: M = UniformRand::rand(&mut thread_rng());
            match first.checked_pow(second.to_u32().unwrap()) {
                Some(value) => check_pow_without_expected_parameters(first, second, value),
                None => check_pow_overflows(first, second),
            }

            check_pow_without_expected_parameters(first, M::zero(), I::one());
            check_pow_without_expected_parameters(first, M::one(), first);
        }

        // Test corner cases for exponentiation.
        check_pow_overflows(I::MAX, M::MAX);
        check_pow_without_expected_parameters(I::MIN, M::zero(), I::one());
        check_pow_without_expected_parameters(I::MAX, M::zero(), I::one());
        check_pow_without_expected_parameters(I::MIN, M::one(), I::MIN);
        check_pow_without_expected_parameters(I::MAX, M::one(), I::MAX);
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_pow = | name: String, first: I, second: M | {
            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::<Circuit, M>::new(mode_b, second);
            match first.checked_pow(second.to_u32().unwrap()) {
                Some(value) => check_pow_checked::<I, M>(&name, value, &a, &b, num_constants, num_public, num_private, num_constraints),
                None => {
                    match (mode_a, mode_b) {
                        (Mode::Constant, Mode::Constant) => check_pow_halts(mode_a, mode_b, first, second),
                        _ => check_pow_fails(mode_a, mode_b, first, second)
                    }
                }
            }
        };

        for i in 0..ITERATIONS {
            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: M = UniformRand::rand(&mut thread_rng());

            check_pow(name, first, second);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(name, first, M::one() + M::one());

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(name, first, M::one() + M::one() + M::one());

        }
    }

    // Tests for u8, where exponent is u8

    #[test]
    fn test_u8_constant_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
    }

    // Tests for i8, where exponent is u8

    #[test]
    fn test_i8_constant_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
    }

    // Tests for u16, where exponent is u8

    #[test]
    fn test_u16_constant_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_public_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
    }

    // Tests for i16, where exponent is u8

    #[test]
    fn test_i16_constant_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_public_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
    }

    // Tests for u32, where exponent is u8

    #[test]
    fn test_u32_constant_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_public_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
    }

    // Tests for i32, where exponent is u8

    #[test]
    fn test_i32_constant_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_public_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
    }

    // Tests for u64, where exponent is u8

    #[test]
    fn test_u64_constant_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_public_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
    }

    // Tests for i64, where exponent is u8

    #[test]
    fn test_i64_constant_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_public_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
    }

    // Tests for u128, where exponent is u8

    #[test]
    fn test_u128_constant_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_public_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
    }

    // Tests for i128, where exponent is u8

    #[test]
    fn test_i128_constant_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_public_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
    }

    // Tests for u8, where exponent is u16

    #[test]
    fn test_u8_constant_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_public_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
    }

    // Tests for i8, where exponent is u16

    #[test]
    fn test_i8_constant_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_public_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
    }

    // Tests for u16, where exponent is u16

    #[test]
    fn test_u16_constant_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_public_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
    }

    // Tests for i16, where exponent is u16

    #[test]
    fn test_i16_constant_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_public_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
    }

    // Tests for u32, where exponent is u16

    #[test]
    fn test_u32_constant_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_public_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
    }

    // Tests for i32, where exponent is u16

    #[test]
    fn test_i32_constant_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_public_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
    }

    // Tests for u64, where exponent is u16

    #[test]
    fn test_u64_constant_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_public_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
    }

    // Tests for i64, where exponent is u16

    #[test]
    fn test_i64_constant_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_public_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
    }

    // Tests for u128, where exponent is u16

    #[test]
    fn test_u128_constant_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_public_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
    }

    // Tests for i128, where exponent is u16

    #[test]
    fn test_i128_constant_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_public_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
    }

    // Tests for u8, where exponent is u32

    #[test]
    fn test_u8_constant_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_public_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
    }

    // Tests for i8, where exponent is u32

    #[test]
    fn test_i8_constant_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_public_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
    }

    // Tests for u16, where exponent is u32

    #[test]
    fn test_u16_constant_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_public_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
    }

    // Tests for i16, where exponent is u32

    #[test]
    fn test_i16_constant_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_public_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
    }

    // Tests for u32, where exponent is u32

    #[test]
    fn test_u32_constant_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_public_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
    }

    // Tests for i32, where exponent is u32

    #[test]
    fn test_i32_constant_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_public_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
    }

    // Tests for u64, where exponent is u32

    #[test]
    fn test_u64_constant_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_public_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
    }

    // Tests for i64, where exponent is u32

    #[test]
    fn test_i64_constant_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_public_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
    }

    // Tests for u128, where exponent is u32

    #[test]
    fn test_u128_constant_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_public_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
    }

    // Tests for i128, where exponent is u32

    #[test]
    fn test_i128_constant_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_public_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
    }
}
