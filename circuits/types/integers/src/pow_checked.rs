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

use crate::helpers::mul_with_carry::MulWithCarry;

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

impl<E: Environment, I: IntegerType, M: Magnitude> Metadata<dyn PowChecked<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, M>);
    type OutputType = IntegerCircuitType<E, I>;

    fn count(case: &Self::Case) -> Count {
        match (case.0.eject_mode(), case.1.eject_mode()) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            _ => {
                let (lhs, rhs) = case;

                let mut total_count = count!(Integer<E, I>, One<Boolean = Boolean<E>>, &());
                let mut result_type = output_type!(Integer<E, I>, One<Boolean = Boolean<E>>, ());

                for bit in rhs.clone().bits_le.into_iter().rev() {
                    // Determine the cost and output type of `result = (&result).mul_checked(&result);`.
                    let case = (result_type.clone(), result_type);
                    total_count = total_count + count!(Self, MulChecked<Self, Output = Self>, &case);
                    result_type = output_type!(Self, MulChecked<Self, Output = Self>, case);

                    // Determine the cost and output type of `result_times_self`. This differs for the the signed and unsigned cases.
                    let result_times_self_type = if I::is_signed() {
                        // Determine the count and output type  of `let (product, carry) = Self::mul_with_carry(&(&result).abs_wrapped(), &self.abs_wrapped());`
                        total_count = total_count + count!(Self, AbsWrapped<Output = Self>, &result_type);
                        let result_abs_wrapped_type =
                            output_type!(Self, AbsWrapped<Output = Self>, result_type.clone());

                        let case = lhs.clone();
                        total_count = total_count + count!(Self, AbsWrapped<Output = Self>, &case);
                        let lhs_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, case);

                        let case = (result_abs_wrapped_type, lhs_abs_wrapped_type);
                        total_count =
                            total_count + count!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, &case);
                        let (product_type, carry_type) =
                            output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, case);

                        // Determine the count and output type of `let carry_bits_nonzero = carry.iter().fold(Boolean::constant(false), |a, b| a | b);`.
                        let (count, carry_bits_nonzero_type) = carry_type.into_iter().fold(
                            (Count::zero(), CircuitType::from(Boolean::constant(false))),
                            |(cummulative_count, prev_type), next_type| {
                                let case = (prev_type, next_type);
                                let count = count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                                let output_type =
                                    output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);
                                (cummulative_count + count, output_type)
                            },
                        );
                        total_count = total_count + count;

                        // Determine the count and output type of `let operands_same_sign = &result.msb().is_equal(self.msb());`.
                        total_count = total_count + count!(Self, MSB<Boolean = Boolean<E>>, &result_type);
                        let result_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, result_type.clone());

                        total_count = total_count + count!(Self, MSB<Boolean = Boolean<E>>, &lhs);
                        let lhs_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, lhs.clone());

                        let case = (result_msb_type, lhs_msb_type);
                        total_count = total_count + count!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, &case);
                        let operands_same_sign_type =
                            output_type!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, case);

                        // Determine the count and output tupe of `let positive_product_overflows = operands_same_sign & product.msb();`.
                        total_count = total_count + count!(Self, MSB<Boolean = Boolean<E>>, &product_type);
                        let product_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, product_type.clone());

                        let case = (operands_same_sign_type.clone(), product_msb_type.clone());
                        total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                        let positive_product_overflows_type =
                            output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

                        // Determine the count and output type of `negative_product_underflows`.
                        let negative_product_underflows_type = {
                            // Determine the count and output type of `let lower_product_bits_nonzero = product.bits_le[..(I::BITS as usize - 1)].iter().fold(Boolean::constant(false), |a, b| a | b);`.
                            let (count, lower_product_bits_nonzero_type) =
                                product_type.bits_le[..(I::BITS as usize - 1)].iter().fold(
                                    (Count::zero(), CircuitType::from(Boolean::constant(false))),
                                    |(cummulative_count, prev_type), next_type| {
                                        let case = (prev_type, next_type.clone());
                                        let count = count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                                        let output_type =
                                            output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);
                                        (cummulative_count + count, output_type)
                                    },
                                );
                            total_count = total_count + count;

                            // Determine the count and output type of `let negative_product_lt_or_eq_signed_min = !product.msb() | (product.msb() & !lower_product_bits_nonzero);`.
                            total_count = total_count + count!(Boolean<E>, Not<Output = Boolean<E>>, &product_msb_type);
                            let product_msb_not_type =
                                output_type!(Boolean<E>, Not<Output = Boolean<E>>, product_msb_type.clone());

                            total_count = total_count
                                + count!(Boolean<E>, Not<Output = Boolean<E>>, &lower_product_bits_nonzero_type);
                            let lower_product_bits_nonzero_not_type = output_type!(
                                Boolean<E>,
                                Not<Output = Boolean<E>>,
                                lower_product_bits_nonzero_type.clone()
                            );

                            let case = (product_msb_type, lower_product_bits_nonzero_not_type);
                            total_count =
                                total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                            let product_msb_or_not_lower_product_bits_nonzero_type =
                                output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

                            let case = (product_msb_not_type, product_msb_or_not_lower_product_bits_nonzero_type);
                            total_count =
                                total_count + count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                            let negative_product_lt_or_eq_signed_min_type =
                                output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);

                            // Determine the count and output type of `!operands_same_sign & !negative_product_lt_or_eq_signed_min`.
                            total_count =
                                total_count + count!(Boolean<E>, Not<Output = Boolean<E>>, &operands_same_sign_type);
                            let operands_same_sign_not_type =
                                output_type!(Boolean<E>, Not<Output = Boolean<E>>, operands_same_sign_type.clone());

                            total_count = total_count
                                + count!(
                                    Boolean<E>,
                                    Not<Output = Boolean<E>>,
                                    &negative_product_lt_or_eq_signed_min_type
                                );
                            let negative_product_lt_or_eq_signed_min_not_type = output_type!(
                                Boolean<E>,
                                Not<Output = Boolean<E>>,
                                negative_product_lt_or_eq_signed_min_type.clone()
                            );

                            let case = (operands_same_sign_not_type, negative_product_lt_or_eq_signed_min_not_type);
                            total_count =
                                total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);

                            output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case)
                        };

                        // Determine the count and cost of `let overflow = carry_bits_nonzero | positive_product_overflows | negative_product_underflows;`.
                        let case = (carry_bits_nonzero_type, positive_product_overflows_type);
                        total_count = total_count + count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                        let carry_bits_nonzero_or_positive_product_overflows_type =
                            output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);

                        let case =
                            (carry_bits_nonzero_or_positive_product_overflows_type, negative_product_underflows_type);
                        total_count = total_count + count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                        let overflow_type = output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);

                        // Determine the cost of `E::assert_eq(overflow & bit, E::zero());`.
                        let case = (overflow_type, bit.clone());
                        total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                        let overflow_and_bit_type =
                            output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

                        match overflow_and_bit_type.is_constant() {
                            true => (), // Do nothing.
                            false => total_count = total_count + Count::is(0, 0, 0, 1),
                        }

                        // Determine the count and output type of `Self::ternary(operands_same_sign, &product, &(!&product).add_wrapped(&Self::one()))`.
                        total_count = total_count + count!(Self, One<Boolean = Boolean<E>>, &());
                        let one_type = output_type!(Self, One<Boolean = Boolean<E>>, ());

                        total_count = total_count + count!(Self, Not<Output = Self>, &product_type);
                        let product_not_type = output_type!(Self, Not<Output = Self>, product_type.clone());

                        let case = (product_not_type, one_type);
                        total_count = total_count + count!(Self, AddWrapped<Self, Output = Self>, &case);
                        let product_not_add_wrapped_one_type =
                            output_type!(Self, AddWrapped<Self, Output = Self>, case);

                        let case = (operands_same_sign_type, product_type, product_not_add_wrapped_one_type);
                        total_count = total_count + count!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, &case);

                        output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case)
                    } else {
                        // Determine the count and output type of `let (product, carry) = Self::mul_with_carry(&result, self);`.
                        let case = (result_type.clone(), lhs.clone());
                        total_count =
                            total_count + count!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, &case);
                        let (product_type, carry_type) =
                            output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, case);

                        // Determine the count and output type of `let overflow = carry.iter().fold(Boolean::constant(false), |a, b| a | b);`.
                        let (count, overflow_type) = carry_type.into_iter().fold(
                            (Count::zero(), CircuitType::from(Boolean::constant(false))),
                            |(cummulative_count, prev_type), next_type| {
                                let case = (prev_type, next_type);
                                let count = count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                                let output_type =
                                    output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);
                                (cummulative_count + count, output_type)
                            },
                        );
                        total_count = total_count + count;

                        // Determine the count and output type of `E::assert_eq(overflow & bit, E::zero());`.
                        let case = (overflow_type, bit.clone());
                        total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                        let overflow_and_bit_type =
                            output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);
                        match overflow_and_bit_type.is_constant() {
                            true => (), // Do nothing.
                            false => total_count = total_count + Count::is(0, 0, 0, 1),
                        }

                        // Return the product of `self` and `other`.
                        product_type
                    };

                    // Determine the cost and output type of `result = Self::ternary(bit, &result_times_self, &result);`.
                    let case = (bit, result_times_self_type, result_type);
                    total_count = total_count + count!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, &case);
                    result_type = output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case);
                }

                match (lhs.eject_mode(), rhs.eject_mode()) {
                    (Mode::Constant, Mode::Public) | (Mode::Constant, Mode::Private) => {
                        match I::is_signed() {
                            // Note: We need to covert the `Count` to an upper bound since there are certain optimizations we cannot statically account for.
                            true => total_count.to_upper_bound(),
                            false => total_count,
                        }
                    }
                    _ => total_count,
                }
            }
        }
    }

    // TODO: Check for overflow
    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs) = case;

        let mut result_type = output_type!(Integer<E, I>, One<Boolean = Boolean<E>>, ());

        for bit in rhs.clone().bits_le.into_iter().rev() {
            // Determine the output type of `result = (&result).mul_wrapped(&result);`.
            let case = (result_type.clone(), result_type);
            result_type = output_type!(Self, MulWrapped<Self, Output = Self>, case);

            // Determine the output type of `result_times_self`. This differs for the the signed and unsigned cases.
            let result_times_self_type = if I::is_signed() {
                // Determine the output type  of `let (product, carry) = Self::mul_with_carry(&(&result).abs_wrapped(), &self.abs_wrapped());`
                let result_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, result_type.clone());

                let case = lhs.clone();
                let lhs_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, case);

                let case = (result_abs_wrapped_type, lhs_abs_wrapped_type);
                let (product_type, _carry_type) =
                    output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, case);

                // Determine the output type of `let operands_same_sign = &result.msb().is_equal(self.msb());`.
                let result_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, result_type.clone());

                let lhs_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, lhs.clone());

                let case = (result_msb_type, lhs_msb_type);
                let operands_same_sign_type = output_type!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, case);

                // Determine the output type of `Self::ternary(operands_same_sign, &product, &(!&product).add_wrapped(&Self::one()))`.
                let one_type = output_type!(Self, One<Boolean = Boolean<E>>, ());

                let product_not_type = output_type!(Self, Not<Output = Self>, product_type.clone());

                let case = (product_not_type, one_type);
                let product_not_add_wrapped_one_type = output_type!(Self, AddWrapped<Self, Output = Self>, case);

                let case = (operands_same_sign_type, product_type, product_not_add_wrapped_one_type);

                output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case)
            } else {
                // Determine the output type of `let (product, carry) = Self::mul_with_carry(&result, self);`.
                let case = (result_type.clone(), lhs.clone());
                let (product_type, _carry_type) =
                    output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, case);

                // Return the product of `self` and `other`.
                product_type
            };

            // Determine the output type of `result = Self::ternary(bit, &result_times_self, &result);`.
            let case = (bit, result_times_self_type, result_type);
            result_type = output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case);
        }
        result_type
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utilities::*;
    use snarkvm_circuits_environment::Circuit;
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
    ) {
        println!("\n{}", name);
        println!("{:?} ^ {:?}", first, second);
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        match first.checked_pow(&second.to_u32().unwrap()) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.pow_checked(&b);
                assert_eq!(expected, candidate.eject_value());

                let case = (IntegerCircuitType::from(a), IntegerCircuitType::from(b));
                assert_count!(PowChecked(Integer<I>, Integer<M>) => Integer<I>, &case);
                assert_output_type!(PowChecked(Integer<I>, Integer<M>) => Integer<I>, case, candidate);
            }),
            None => match (mode_a, mode_b) {
                (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::pow_checked),
                _ => Circuit::scope(name, || {
                    let _candidate = a.pow_checked(&b);

                    let case = (IntegerCircuitType::from(a), IntegerCircuitType::from(b));
                    assert_count_fails!(PowChecked(Integer<I>, Integer<M>) => Integer<I>, &case);
                }),
            },
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: M = UniformRand::rand(&mut test_rng());

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second, mode_a, mode_b);

            let name = format!("Pow Zero: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::zero(), mode_a, mode_b);

            let name = format!("Pow One: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one(), mode_a, mode_b);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one(), mode_a, mode_b);

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one() + M::one(), mode_a, mode_b);
        }

        // Test corner cases for exponentiation.
        check_pow("MAX ** MAX", I::MAX, M::MAX, mode_a, mode_b);
        check_pow("MIN ** 0", I::MIN, M::zero(), mode_a, mode_b);
        check_pow("MAX ** 0", I::MAX, M::zero(), mode_a, mode_b);
        check_pow("MIN ** 1", I::MIN, M::one(), mode_a, mode_b);
        check_pow("MAX ** 1", I::MAX, M::one(), mode_a, mode_b);
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, u8, pow);
    test_integer_binary!(run_test, i8, u16, pow);
    test_integer_binary!(run_test, i8, u32, pow);

    test_integer_binary!(run_test, i16, u8, pow);
    test_integer_binary!(run_test, i16, u16, pow);
    test_integer_binary!(run_test, i16, u32, pow);

    test_integer_binary!(run_test, i32, u8, pow);
    test_integer_binary!(run_test, i32, u16, pow);
    test_integer_binary!(run_test, i32, u32, pow);

    test_integer_binary!(run_test, i64, u8, pow);
    test_integer_binary!(run_test, i64, u16, pow);
    test_integer_binary!(run_test, i64, u32, pow);

    test_integer_binary!(run_test, i128, u8, pow);
    test_integer_binary!(run_test, i128, u16, pow);
    test_integer_binary!(run_test, i128, u32, pow);

    test_integer_binary!(run_test, u8, u8, pow);
    test_integer_binary!(run_test, u8, u16, pow);
    test_integer_binary!(run_test, u8, u32, pow);

    test_integer_binary!(run_test, u16, u8, pow);
    test_integer_binary!(run_test, u16, u16, pow);
    test_integer_binary!(run_test, u16, u32, pow);

    test_integer_binary!(run_test, u32, u8, pow);
    test_integer_binary!(run_test, u32, u16, pow);
    test_integer_binary!(run_test, u32, u32, pow);

    test_integer_binary!(run_test, u64, u8, pow);
    test_integer_binary!(run_test, u64, u16, pow);
    test_integer_binary!(run_test, u64, u32, pow);

    test_integer_binary!(run_test, u128, u8, pow);
    test_integer_binary!(run_test, u128, u16, pow);
    test_integer_binary!(run_test, u128, u32, pow);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, u8, pow, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, u8, pow, exhaustive);
}
