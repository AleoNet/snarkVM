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

impl<E: Environment, I: IntegerType, M: Magnitude> PowChecked<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn pow_checked(&self, other: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            match self.eject_value().checked_pow(&other.eject_value().to_u32().unwrap()) {
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

                let result_times_self = if I::is_signed() {
                    // Multiply the absolute value of `self` and `other` in the base field.
                    // Note that it is safe to use abs_wrapped since we want I::MIN to be interpreted as an unsigned number.
                    let (product, carry) = Self::mul_with_carry(&(&result).abs_wrapped(), &self.abs_wrapped());

                    // We need to check that the abs(a) * abs(b) did not exceed the unsigned maximum.
                    let carry_bits_nonzero = carry.iter().fold(Boolean::constant(false), |a, b| a | b);

                    // If the product should be positive, then it cannot exceed the signed maximum.
                    let operands_same_sign = &result.msb().is_equal(self.msb());
                    let positive_product_overflows = operands_same_sign & product.msb();

                    // If the product should be negative, then it cannot exceed the absolute value of the signed minimum.
                    let negative_product_underflows = {
                        let lower_product_bits_nonzero = product.bits_le[..(I::BITS as usize - 1)]
                            .iter()
                            .fold(Boolean::constant(false), |a, b| a | b);
                        let negative_product_lt_or_eq_signed_min =
                            !product.msb() | (product.msb() & !lower_product_bits_nonzero);
                        !operands_same_sign & !negative_product_lt_or_eq_signed_min
                    };

                    let overflow = carry_bits_nonzero | positive_product_overflows | negative_product_underflows;
                    E::assert_eq(overflow & bit, E::zero());

                    // Return the product of `self` and `other` with the appropriate sign.
                    Self::ternary(operands_same_sign, &product, &(!&product).add_wrapped(&Self::one()))
                } else {
                    let (product, carry) = Self::mul_with_carry(&result, self);

                    // For unsigned multiplication, check that the none of the carry bits are set.
                    let overflow = carry.iter().fold(Boolean::constant(false), |a, b| a | b);
                    E::assert_eq(overflow & bit, E::zero());

                    // Return the product of `self` and `other`.
                    product
                };

                result = Self::ternary(bit, &result_times_self, &result);
            }
            result
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metrics<dyn PowChecked<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            (Mode::Constant, _) | (_, Mode::Constant) => {
                let mul_count = count!(Integer<E, I>, MulWrapped<Integer<E, I>, Output=Integer<E, I>>, case);
                (2 * M::BITS * mul_count) + Count::is(2 * I::BITS, 0, I::BITS, I::BITS)
            }
            (_, _) => {
                let mul_count = count!(Integer<E, I>, MulWrapped<Integer<E, I>, Output=Integer<E, I>>, case);
                (2 * M::BITS * mul_count) + Count::is(2 * I::BITS, 0, I::BITS, I::BITS)
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> OutputMode<dyn PowChecked<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, CircuitType<Integer<E, M>>);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, (case.1.mode(), &case.1)) {
            (Mode::Constant, (Mode::Constant, _)) => Mode::Constant,
            (Mode::Constant, (mode, _)) => match mode {
                Mode::Constant => Mode::Constant,
                _ => Mode::Private,
            },
            (_, (Mode::Constant, case)) => match case {
                // Determine if the constant is all zeros.
                CircuitType::Constant(constant) => match constant.eject_value().is_zero() {
                    true => Mode::Constant,
                    false => Mode::Private,
                },
                _ => E::halt("The constant is required for the output mode of `pow_wrapped` with a constant."),
            },
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use super::*;
    use crate::test_utilities::*;
    use snarkvm_circuits_environment::{count_is, count_less_than, Circuit, UpdatableCount};
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    // Lowered to 4; we run (~5 * ITERATIONS) cases for most tests.
    const ITERATIONS: u64 = 4;

    fn check_pow<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
        count: UpdatableCount
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        match first.checked_pow(&second.to_u32().unwrap()) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.pow_checked(&b);
                assert_eq!(expected, candidate.eject_value());
                count.assert_matches(
                    Circuit::num_constants_in_scope(),
                    Circuit::num_public_in_scope(),
                    Circuit::num_private_in_scope(),
                    Circuit::num_constraints_in_scope(),
                );
                // assert_output_mode!(PowChecked(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, CircuitType::from(&b)), candidate);
                assert!(Circuit::is_satisfied());
            }),
            None => {
                match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::pow_checked),
                    _ => Circuit::scope(name, || {
                        let _candidate = a.pow_checked(&b);
                        count.assert_matches(
                            Circuit::num_constants_in_scope(),
                            Circuit::num_public_in_scope(),
                            Circuit::num_private_in_scope(),
                            Circuit::num_constraints_in_scope(),
                        );
                        assert!(!Circuit::is_satisfied());
                    }),
                }
            }
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode, count: UpdatableCount) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: M = UniformRand::rand(&mut test_rng());

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second, mode_a, mode_b, count);

            let name = format!("Pow Zero: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::zero(), mode_a, mode_b, count);

            let name = format!("Pow One: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one(), mode_a, mode_b, count);

            let name = format!("Zero Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, I::zero(), second, mode_a, mode_b, count);

            let name = format!("One Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, I::one(), second, mode_a, mode_b, count);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one(), mode_a, mode_b, count);

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one() + M::one(), mode_a, mode_b, count);
        }

        // Test corner cases for exponentiation.
        check_pow("MAX ** MAX", I::MAX, M::MAX, mode_a, mode_b, count);
        check_pow("MIN ** 0", I::MIN, M::zero(), mode_a, mode_b, count);
        check_pow("MAX ** 0", I::MAX, M::zero(), mode_a, mode_b, count);
        check_pow("MIN ** 1", I::MIN, M::one(), mode_a, mode_b, count);
        check_pow("MAX ** 1", I::MAX, M::one(), mode_a, mode_b, count);
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode, count: UpdatableCount)
    where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow(&name, first, second, mode_a, mode_b, count);
            }
        }
    }

    // Tests for u8 ^ u8.

    test_integer_case!(run_test, u8, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(8, 0, 0, 0));
    test_integer_case!(run_test, u8, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(200, 0, 392, 420));
    test_integer_case!(run_test, u8, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(200, 0, 392, 420));
    test_integer_case!(run_test, u8, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(72, 0, 359, 389));
    test_integer_case!(run_test, u8, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(16, 0, 431, 461));
    test_integer_case!(run_test, u8, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(16, 0, 431, 461));
    test_integer_case!(run_test, u8, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(72, 0, 359, 389));
    test_integer_case!(run_test, u8, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(16, 0, 431, 461));
    test_integer_case!(run_test, u8, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(16, 0, 431, 461));

    // Tests for u8 ^ u16.

    test_integer_case!(run_test, u8, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(8, 0, 0, 0));
    test_integer_case!(run_test, u8, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(392, 0, 840, 900));
    test_integer_case!(run_test, u8, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(392, 0, 840, 900));
    test_integer_case!(run_test, u8, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(136, 0, 743, 805));
    test_integer_case!(run_test, u8, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(16, 0, 887, 949));
    test_integer_case!(run_test, u8, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(16, 0, 887, 949));
    test_integer_case!(run_test, u8, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(136, 0, 743, 805));
    test_integer_case!(run_test, u8, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(16, 0, 887, 949));
    test_integer_case!(run_test, u8, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(16, 0, 887, 949));

    // Tests for u8 ^ u32.

    test_integer_case!(run_test, u8, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(8, 0, 0, 0));
    test_integer_case!(run_test, u8, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(776, 0, 1736, 1860));
    test_integer_case!(run_test, u8, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(776, 0, 1736, 1860));
    test_integer_case!(run_test, u8, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(264, 0, 1511, 1637));
    test_integer_case!(run_test, u8, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(16, 0, 1799, 1925));
    test_integer_case!(run_test, u8, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(16, 0, 1799, 1925));
    test_integer_case!(run_test, u8, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(264, 0, 1511, 1637));
    test_integer_case!(run_test, u8, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(16, 0, 1799, 1925));
    test_integer_case!(run_test, u8, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(16, 0, 1799, 1925));

    // Tests for i8 ^ u8.

    test_integer_case!(run_test, i8, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(8, 0, 0, 0));
    test_integer_case!(run_test, i8, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(584, 0, 1162, 1225));
    test_integer_case!(run_test, i8, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(584, 0, 1162, 1225));
    test_integer_case!(run_test, i8, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(384, 0, 1301, 1375));
    test_integer_case!(run_test, i8, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(384, 0, 1373, 1447));
    test_integer_case!(run_test, i8, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(384, 0, 1373, 1447));
    test_integer_case!(run_test, i8, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(384, 0, 1301, 1375));
    test_integer_case!(run_test, i8, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(384, 0, 1373, 1447));
    test_integer_case!(run_test, i8, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(384, 0, 1373, 1447));

    // Tests for i8 ^ u16.

    test_integer_case!(run_test, i8, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(8, 0, 0, 0));
    test_integer_case!(run_test, i8, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(1160, 0, 2490, 2625));
    test_integer_case!(run_test, i8, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(1160, 0, 2490, 2625));
    test_integer_case!(run_test, i8, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(768, 0, 2709, 2863));
    test_integer_case!(run_test, i8, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(768, 0, 2853, 3007));
    test_integer_case!(run_test, i8, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(768, 0, 2853, 3007));
    test_integer_case!(run_test, i8, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(768, 0, 2709, 2863));
    test_integer_case!(run_test, i8, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(768, 0, 2853, 3007));
    test_integer_case!(run_test, i8, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(768, 0, 2853, 3007));

    // Tests for i8 ^ u32.

    test_integer_case!(run_test, i8, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(8, 0, 0, 0));
    test_integer_case!(run_test, i8, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(2312, 0, 5146, 5425));
    test_integer_case!(run_test, i8, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(2312, 0, 5146, 5425));
    test_integer_case!(run_test, i8, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(1536, 0, 5525, 5839));
    test_integer_case!(run_test, i8, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(1536, 0, 5813, 6127));
    test_integer_case!(run_test, i8, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(1536, 0, 5813, 6127));
    test_integer_case!(run_test, i8, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(1536, 0, 5525, 5839));
    test_integer_case!(run_test, i8, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(1536, 0, 5813, 6127));
    test_integer_case!(run_test, i8, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(1536, 0, 5813, 6127));

    // Tests for u16 ^ u8.

    test_integer_case!(run_test, u16, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(16, 0, 0, 0));
    test_integer_case!(run_test, u16, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(400, 0, 784, 812));
    test_integer_case!(run_test, u16, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(400, 0, 784, 812));
    test_integer_case!(run_test, u16, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(144, 0, 719, 749));
    test_integer_case!(run_test, u16, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(32, 0, 855, 885));
    test_integer_case!(run_test, u16, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(32, 0, 855, 885));
    test_integer_case!(run_test, u16, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(144, 0, 719, 749));
    test_integer_case!(run_test, u16, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(32, 0, 855, 885));
    test_integer_case!(run_test, u16, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(32, 0, 855, 885));

    // Tests for u16 ^ u16.

    test_integer_case!(run_test, u16, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(16, 0, 0, 0));
    test_integer_case!(run_test, u16, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(784, 0, 1680, 1740));
    test_integer_case!(run_test, u16, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(784, 0, 1680, 1740));
    test_integer_case!(run_test, u16, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(272, 0, 1487, 1549));
    test_integer_case!(run_test, u16, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(32, 0, 1759, 1821));
    test_integer_case!(run_test, u16, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(32, 0, 1759, 1821));
    test_integer_case!(run_test, u16, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(272, 0, 1487, 1549));
    test_integer_case!(run_test, u16, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(32, 0, 1759, 1821));
    test_integer_case!(run_test, u16, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(32, 0, 1759, 1821));

    // Tests for u16 ^ u32.

    test_integer_case!(run_test, u16, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(16, 0, 0, 0));
    test_integer_case!(run_test, u16, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(1552, 0, 3472, 3596));
    test_integer_case!(run_test, u16, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(1552, 0, 3472, 3596));
    test_integer_case!(run_test, u16, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(528, 0, 3023, 3149));
    test_integer_case!(run_test, u16, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(32, 0, 3567, 3693));
    test_integer_case!(run_test, u16, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(32, 0, 3567, 3693));
    test_integer_case!(run_test, u16, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(528, 0, 3023, 3149));
    test_integer_case!(run_test, u16, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(32, 0, 3567, 3693));
    test_integer_case!(run_test, u16, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(32, 0, 3567, 3693));

    // Tests for i16 ^ u8.

    test_integer_case!(run_test, i16, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(16, 0, 0, 0));
    test_integer_case!(run_test, i16, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(1168, 0, 2226, 2289));
    test_integer_case!(run_test, i16, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(1168, 0, 2226, 2289));
    test_integer_case!(run_test, i16, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(768, 0, 2485, 2559));
    test_integer_case!(run_test, i16, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(768, 0, 2621, 2695));
    test_integer_case!(run_test, i16, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(768, 0, 2621, 2695));
    test_integer_case!(run_test, i16, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(768, 0, 2485, 2559));
    test_integer_case!(run_test, i16, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(768, 0, 2621, 2695));
    test_integer_case!(run_test, i16, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(768, 0, 2621, 2695));

    // Tests for i16 ^ u16.

    test_integer_case!(run_test, i16, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(16, 0, 0, 0));
    test_integer_case!(run_test, i16, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(2320, 0, 4770, 4905));
    test_integer_case!(run_test, i16, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(2320, 0, 4770, 4905));
    test_integer_case!(run_test, i16, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(1536, 0, 5173, 5327));
    test_integer_case!(run_test, i16, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(1536, 0, 5445, 5599));
    test_integer_case!(run_test, i16, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(1536, 0, 5445, 5599));
    test_integer_case!(run_test, i16, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(1536, 0, 5173, 5327));
    test_integer_case!(run_test, i16, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(1536, 0, 5445, 5599));
    test_integer_case!(run_test, i16, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(1536, 0, 5445, 5599));

    // Tests for i16 ^ u32.

    test_integer_case!(run_test, i16, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(16, 0, 0, 0));
    test_integer_case!(run_test, i16, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(4624, 0, 9858, 10137));
    test_integer_case!(run_test, i16, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(4624, 0, 9858, 10137));
    test_integer_case!(run_test, i16, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(3072, 0, 10549, 10863));
    test_integer_case!(run_test, i16, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(3072, 0, 11093, 11407));
    test_integer_case!(run_test, i16, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(3072, 0, 11093, 11407));
    test_integer_case!(run_test, i16, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(3072, 0, 10549, 10863));
    test_integer_case!(run_test, i16, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(3072, 0, 11093, 11407));
    test_integer_case!(run_test, i16, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(3072, 0, 11093, 11407));

    // Tests for u32 ^ u8.

    test_integer_case!(run_test, u32, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(32, 0, 0, 0));
    test_integer_case!(run_test, u32, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(800, 0, 1568, 1596));
    test_integer_case!(run_test, u32, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(800, 0, 1568, 1596));
    test_integer_case!(run_test, u32, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(288, 0, 1439, 1469));
    test_integer_case!(run_test, u32, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(64, 0, 1703, 1733));
    test_integer_case!(run_test, u32, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(64, 0, 1703, 1733));
    test_integer_case!(run_test, u32, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(288, 0, 1439, 1469));
    test_integer_case!(run_test, u32, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(64, 0, 1703, 1733));
    test_integer_case!(run_test, u32, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(64, 0, 1703, 1733));

    // Tests for u32 ^ u16.

    test_integer_case!(run_test, u32, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(32, 0, 0, 0));
    test_integer_case!(run_test, u32, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(1568, 0, 3360, 3420));
    test_integer_case!(run_test, u32, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(1568, 0, 3360, 3420));
    test_integer_case!(run_test, u32, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(544, 0, 2975, 3037));
    test_integer_case!(run_test, u32, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(64, 0, 3503, 3565));
    test_integer_case!(run_test, u32, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(64, 0, 3503, 3565));
    test_integer_case!(run_test, u32, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(544, 0, 2975, 3037));
    test_integer_case!(run_test, u32, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(64, 0, 3503, 3565));
    test_integer_case!(run_test, u32, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(64, 0, 3503, 3565));

    // Tests for u32 ^ u32.

    test_integer_case!(run_test, u32, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(32, 0, 0, 0));
    test_integer_case!(run_test, u32, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(3104, 0, 6944, 7068));
    test_integer_case!(run_test, u32, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(3104, 0, 6944, 7068));
    test_integer_case!(run_test, u32, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(1056, 0, 6047, 6173));
    test_integer_case!(run_test, u32, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(64, 0, 7103, 7229));
    test_integer_case!(run_test, u32, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(64, 0, 7103, 7229));
    test_integer_case!(run_test, u32, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(1056, 0, 6047, 6173));
    test_integer_case!(run_test, u32, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(64, 0, 7103, 7229));
    test_integer_case!(run_test, u32, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(64, 0, 7103, 7229));

    // Tests for i32 ^ u8.

    test_integer_case!(run_test, i32, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(32, 0, 0, 0));
    test_integer_case!(run_test, i32, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(2336, 0, 4354, 4417));
    test_integer_case!(run_test, i32, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(2336, 0, 4354, 4417));
    test_integer_case!(run_test, i32, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(1536, 0, 4853, 4927));
    test_integer_case!(run_test, i32, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(1536, 0, 5117, 5191));
    test_integer_case!(run_test, i32, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(1536, 0, 5117, 5191));
    test_integer_case!(run_test, i32, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(1536, 0, 4853, 4927));
    test_integer_case!(run_test, i32, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(1536, 0, 5117, 5191));
    test_integer_case!(run_test, i32, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(1536, 0, 5117, 5191));

    // Tests for i32 ^ u16.

    test_integer_case!(run_test, i32, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(32, 0, 0, 0));
    test_integer_case!(run_test, i32, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(4640, 0, 9330, 9465));
    test_integer_case!(run_test, i32, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(4640, 0, 9330, 9465));
    test_integer_case!(run_test, i32, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(3072, 0, 10101, 10255));
    test_integer_case!(run_test, i32, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(3072, 0, 10629, 10783));
    test_integer_case!(run_test, i32, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(3072, 0, 10629, 10783));
    test_integer_case!(run_test, i32, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(3072, 0, 10101, 10255));
    test_integer_case!(run_test, i32, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(3072, 0, 10629, 10783));
    test_integer_case!(run_test, i32, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(3072, 0, 10629, 10783));

    // Tests for i32 ^ u32.

    test_integer_case!(run_test, i32, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(32, 0, 0, 0));
    test_integer_case!(run_test, i32, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(9248, 0, 19282, 19561));
    test_integer_case!(run_test, i32, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(9248, 0, 19282, 19561));
    test_integer_case!(run_test, i32, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(6144, 0, 20597, 20911));
    test_integer_case!(run_test, i32, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(6144, 0, 21653, 21967));
    test_integer_case!(run_test, i32, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(6144, 0, 21653, 21967));
    test_integer_case!(run_test, i32, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(6144, 0, 20597, 20911));
    test_integer_case!(run_test, i32, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(6144, 0, 21653, 21967));
    test_integer_case!(run_test, i32, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(6144, 0, 21653, 21967));

    // Tests for u64 ^ u8.

    test_integer_case!(run_test, u64, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(64, 0, 0, 0));
    test_integer_case!(run_test, u64, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(1600, 0, 3136, 3164));
    test_integer_case!(run_test, u64, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(1600, 0, 3136, 3164));
    test_integer_case!(run_test, u64, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(576, 0, 2879, 2909));
    test_integer_case!(run_test, u64, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(128, 0, 3399, 3429));
    test_integer_case!(run_test, u64, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(128, 0, 3399, 3429));
    test_integer_case!(run_test, u64, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(576, 0, 2879, 2909));
    test_integer_case!(run_test, u64, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(128, 0, 3399, 3429));
    test_integer_case!(run_test, u64, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(128, 0, 3399, 3429));

    // Tests for u64 ^ u16.

    test_integer_case!(run_test, u64, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(64, 0, 0, 0));
    test_integer_case!(run_test, u64, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(3136, 0, 6720, 6780));
    test_integer_case!(run_test, u64, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(3136, 0, 6720, 6780));
    test_integer_case!(run_test, u64, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(1088, 0, 5951, 6013));
    test_integer_case!(run_test, u64, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(128, 0, 6991, 7053));
    test_integer_case!(run_test, u64, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(128, 0, 6991, 7053));
    test_integer_case!(run_test, u64, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(1088, 0, 5951, 6013));
    test_integer_case!(run_test, u64, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(128, 0, 6991, 7053));
    test_integer_case!(run_test, u64, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(128, 0, 6991, 7053));

    // Tests for u64 ^ u32.

    test_integer_case!(run_test, u64, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(64, 0, 0, 0));
    test_integer_case!(run_test, u64, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(6208, 0, 13888, 14012));
    test_integer_case!(run_test, u64, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(6208, 0, 13888, 14012));
    test_integer_case!(run_test, u64, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(2112, 0, 12095, 12221));
    test_integer_case!(run_test, u64, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(128, 0, 14175, 14301));
    test_integer_case!(run_test, u64, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(128, 0, 14175, 14301));
    test_integer_case!(run_test, u64, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(2112, 0, 12095, 12221));
    test_integer_case!(run_test, u64, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(128, 0, 14175, 14301));
    test_integer_case!(run_test, u64, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(128, 0, 14175, 14301));

    // Tests for i64 ^ u8.

    test_integer_case!(run_test, i64, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(64, 0, 0, 0));
    test_integer_case!(run_test, i64, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(4672, 0, 8610, 8673));
    test_integer_case!(run_test, i64, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(4672, 0, 8610, 8673));
    test_integer_case!(run_test, i64, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(3072, 0, 9589, 9663));
    test_integer_case!(run_test, i64, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(3072, 0, 10109, 10183));
    test_integer_case!(run_test, i64, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(3072, 0, 10109, 10183));
    test_integer_case!(run_test, i64, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(3072, 0, 9589, 9663));
    test_integer_case!(run_test, i64, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(3072, 0, 10109, 10183));
    test_integer_case!(run_test, i64, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(3072, 0, 10109, 10183));

    // Tests for i64 ^ u16.

    test_integer_case!(run_test, i64, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(64, 0, 0, 0));
    test_integer_case!(run_test, i64, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(9280, 0, 18450, 18585));
    test_integer_case!(run_test, i64, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(9280, 0, 18450, 18585));
    test_integer_case!(run_test, i64, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(6144, 0, 19957, 20111));
    test_integer_case!(run_test, i64, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(6144, 0, 20997, 21151));
    test_integer_case!(run_test, i64, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(6144, 0, 20997, 21151));
    test_integer_case!(run_test, i64, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(6144, 0, 19957, 20111));
    test_integer_case!(run_test, i64, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(6144, 0, 20997, 21151));
    test_integer_case!(run_test, i64, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(6144, 0, 20997, 21151));

    // Tests for i64 ^ u32.

    test_integer_case!(run_test, i64, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(64, 0, 0, 0));
    test_integer_case!(run_test, i64, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(18496, 0, 38130, 38409));
    test_integer_case!(run_test, i64, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(18496, 0, 38130, 38409));
    test_integer_case!(run_test, i64, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(12288, 0, 40693, 41007));
    test_integer_case!(run_test, i64, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(12288, 0, 42773, 43087));
    test_integer_case!(run_test, i64, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(12288, 0, 42773, 43087));
    test_integer_case!(run_test, i64, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(12288, 0, 40693, 41007));
    test_integer_case!(run_test, i64, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(12288, 0, 42773, 43087));
    test_integer_case!(run_test, i64, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(12288, 0, 42773, 43087));

    // Tests for u128 ^ u8.

    test_integer_case!(run_test, u128, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(128, 0, 0, 0));
    test_integer_case!(run_test, u128, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(3720, 0, 8113, 8155));
    test_integer_case!(run_test, u128, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(3720, 0, 8113, 8155));
    test_integer_case!(run_test, u128, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(1152, 0, 7751, 7796));
    test_integer_case!(run_test, u128, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(256, 0, 8783, 8828));
    test_integer_case!(run_test, u128, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(256, 0, 8783, 8828));
    test_integer_case!(run_test, u128, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(1152, 0, 7751, 7796));
    test_integer_case!(run_test, u128, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(256, 0, 8783, 8828));
    test_integer_case!(run_test, u128, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(256, 0, 8783, 8828));

    // Tests for u128 ^ u16.

    test_integer_case!(run_test, u128, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(128, 0, 0, 0));
    test_integer_case!(run_test, u128, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(7312, 0, 17385, 17475));
    test_integer_case!(run_test, u128, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(7312, 0, 17385, 17475));
    test_integer_case!(run_test, u128, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(2176, 0, 16023, 16116));
    test_integer_case!(run_test, u128, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(256, 0, 18087, 18180));
    test_integer_case!(run_test, u128, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(256, 0, 18087, 18180));
    test_integer_case!(run_test, u128, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(2176, 0, 16023, 16116));
    test_integer_case!(run_test, u128, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(256, 0, 18087, 18180));
    test_integer_case!(run_test, u128, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(256, 0, 18087, 18180));

    // Tests for u128 ^ u32.

    test_integer_case!(run_test, u128, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(128, 0, 0, 0));
    test_integer_case!(run_test, u128, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(14496, 0, 35929, 36115));
    test_integer_case!(run_test, u128, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(14496, 0, 35929, 36115));
    test_integer_case!(run_test, u128, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(4224, 0, 32567, 32756));
    test_integer_case!(run_test, u128, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(256, 0, 36695, 36884));
    test_integer_case!(run_test, u128, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(256, 0, 36695, 36884));
    test_integer_case!(run_test, u128, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(4224, 0, 32567, 32756));
    test_integer_case!(run_test, u128, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(256, 0, 36695, 36884));
    test_integer_case!(run_test, u128, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(256, 0, 36695, 36884));

    // Tests for i128 ^ u8.

    test_integer_case!(run_test, i128, u8, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(128, 0, 0, 0));
    test_integer_case!(run_test, i128, u8, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(9864, 0, 18963, 19040));
    test_integer_case!(run_test, i128, u8, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(9864, 0, 18963, 19040));
    test_integer_case!(run_test, i128, u8, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(6144, 0, 21053, 21142));
    test_integer_case!(run_test, i128, u8, Mode::Public, Mode::Public, public_pow_public, count_is!(6144, 0, 22085, 22174));
    test_integer_case!(run_test, i128, u8, Mode::Public, Mode::Private, public_pow_private, count_is!(6144, 0, 22085, 22174));
    test_integer_case!(run_test, i128, u8, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(6144, 0, 21053, 21142));
    test_integer_case!(run_test, i128, u8, Mode::Private, Mode::Public, private_pow_public, count_is!(6144, 0, 22085, 22174));
    test_integer_case!(run_test, i128, u8, Mode::Private, Mode::Private, private_pow_private, count_is!(6144, 0, 22085, 22174));

    // Tests for i128 ^ u16.

    test_integer_case!(run_test, i128, u16, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(128, 0, 0, 0));
    test_integer_case!(run_test, i128, u16, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(19600, 0, 40635, 40800));
    test_integer_case!(run_test, i128, u16, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(19600, 0, 40635, 40800));
    test_integer_case!(run_test, i128, u16, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(12288, 0, 43789, 43974));
    test_integer_case!(run_test, i128, u16, Mode::Public, Mode::Public, public_pow_public, count_is!(12288, 0, 45853, 46038));
    test_integer_case!(run_test, i128, u16, Mode::Public, Mode::Private, public_pow_private, count_is!(12288, 0, 45853, 46038));
    test_integer_case!(run_test, i128, u16, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(12288, 0, 43789, 43974));
    test_integer_case!(run_test, i128, u16, Mode::Private, Mode::Public, private_pow_public, count_is!(12288, 0, 45853, 46038));
    test_integer_case!(run_test, i128, u16, Mode::Private, Mode::Private, private_pow_private, count_is!(12288, 0, 45853, 46038));

    // Tests for i128 ^ u32.

    test_integer_case!(run_test, i128, u32, Mode::Constant, Mode::Constant, constant_pow_constant, count_is!(128, 0, 0, 0));
    test_integer_case!(run_test, i128, u32, Mode::Constant, Mode::Public, constant_pow_public, count_less_than!(39072, 0, 83979, 84320));
    test_integer_case!(run_test, i128, u32, Mode::Constant, Mode::Private, constant_pow_private, count_less_than!(39072, 0, 83979, 84320));
    test_integer_case!(run_test, i128, u32, Mode::Public, Mode::Constant, public_pow_constant, count_less_than!(24576, 0, 89261, 89638));
    test_integer_case!(run_test, i128, u32, Mode::Public, Mode::Public, public_pow_public, count_is!(24576, 0, 93389, 93766));
    test_integer_case!(run_test, i128, u32, Mode::Public, Mode::Private, public_pow_private, count_is!(24576, 0, 93389, 93766));
    test_integer_case!(run_test, i128, u32, Mode::Private, Mode::Constant, private_pow_constant, count_less_than!(24576, 0, 89261, 89638));
    test_integer_case!(run_test, i128, u32, Mode::Private, Mode::Public, private_pow_public, count_is!(24576, 0, 93389, 93766));
    test_integer_case!(run_test, i128, u32, Mode::Private, Mode::Private, private_pow_private, count_is!(24576, 0, 93389, 93766));

    // Exhaustive tests for u8 ^ u8.

    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Constant, Mode::Constant, constant_pow_constant, exhaustive, count_is!(8, 0, 0, 0));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Constant, Mode::Public, constant_pow_public, exhaustive, count_less_than!(200, 0, 392, 420));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Constant, Mode::Private, constant_pow_private, exhaustive, count_less_than!(200, 0, 392, 420));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Public, Mode::Constant, public_pow_constant, exhaustive, count_less_than!(72, 0, 359, 389));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Public, Mode::Public, public_pow_public, exhaustive, count_is!(16, 0, 431, 461));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Public, Mode::Private, public_pow_private, exhaustive, count_is!(16, 0, 431, 461));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Private, Mode::Constant, private_pow_constant, exhaustive, count_less_than!(72, 0, 359, 389));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Private, Mode::Public, private_pow_public, exhaustive, count_is!(16, 0, 431, 461));
    test_integer_case!(#[ignore], run_exhaustive_test, u8, u8, Mode::Private, Mode::Private, private_pow_private, exhaustive, count_is!(16, 0, 431, 461));

    // Exhaustive tests for i8 ^ u8.

    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Constant, Mode::Constant, constant_pow_constant, exhaustive, count_is!(8, 0, 0, 0));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Constant, Mode::Public, constant_pow_public, exhaustive, count_less_than!(584, 0, 1162, 1225));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Constant, Mode::Private, constant_pow_private, exhaustive, count_less_than!(584, 0, 1162, 1225));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Public, Mode::Constant, public_pow_constant, exhaustive, count_less_than!(384, 0, 1301, 1375));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Public, Mode::Public, public_pow_public, exhaustive, count_is!(384, 0, 1373, 1447));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Public, Mode::Private, public_pow_private, exhaustive, count_is!(384, 0, 1373, 1447));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Private, Mode::Constant, private_pow_constant, exhaustive, count_less_than!(384, 0, 1301, 1375));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Private, Mode::Public, private_pow_public, exhaustive, count_is!(384, 0, 1373, 1447));
    test_integer_case!(#[ignore], run_exhaustive_test, i8, u8, Mode::Private, Mode::Private, private_pow_private, exhaustive, count_is!(384, 0, 1373, 1447));
}
