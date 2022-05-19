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

impl<E: Environment, I: IntegerType> Mul<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        self * &other
    }
}

impl<E: Environment, I: IntegerType> Mul<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn mul(self, other: Integer<E, I>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment, I: IntegerType> Mul<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn mul(self, other: &Self) -> Self::Output {
        &self * other
    }
}

impl<E: Environment, I: IntegerType> Mul<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn mul(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output *= other;
        output
    }
}

impl<E: Environment, I: IntegerType> MulAssign<Integer<E, I>> for Integer<E, I> {
    fn mul_assign(&mut self, other: Integer<E, I>) {
        *self *= &other;
    }
}

impl<E: Environment, I: IntegerType> MulAssign<&Integer<E, I>> for Integer<E, I> {
    fn mul_assign(&mut self, other: &Integer<E, I>) {
        // Stores the product of `self` and `other` in `self`.
        *self = self.mul_checked(other);
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn Mul<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, I>);
    type OutputType = IntegerCircuitType<E, I>;

    fn count(case: &Self::Case) -> Count {
        count!(Self, MulChecked<Self, Output = Self>, case)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        output_type!(Self, MulChecked<Self, Output = Self>, case)
    }
}

impl<E: Environment, I: IntegerType> MulChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn mul_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the product and return the new constant.
            match self.eject_value().checked_mul(&other.eject_value()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on multiplication of two constants"),
            }
        } else if I::is_signed() {
            // Multiply the absolute value of `self` and `other` in the base field.
            // Note that it is safe to use abs_wrapped since we want I::MIN to be interpreted as an unsigned number.
            let (product, carry) = Self::mul_with_carry(&self.abs_wrapped(), &other.abs_wrapped());

            // We need to check that the abs(a) * abs(b) did not exceed the unsigned maximum.
            let carry_bits_nonzero = carry.iter().fold(Boolean::constant(false), |a, b| a | b);

            // If the product should be positive, then it cannot exceed the signed maximum.
            let operands_same_sign = &self.msb().is_equal(other.msb());
            let positive_product_overflows = operands_same_sign & product.msb();

            // If the product should be negative, then it cannot exceed the absolute value of the signed minimum.
            let negative_product_underflows = {
                let lower_product_bits_nonzero =
                    product.bits_le[..(I::BITS as usize - 1)].iter().fold(Boolean::constant(false), |a, b| a | b);
                let negative_product_lt_or_eq_signed_min =
                    !product.msb() | (product.msb() & !lower_product_bits_nonzero);
                !operands_same_sign & !negative_product_lt_or_eq_signed_min
            };

            // Ensure there are no overflows.
            let overflow = carry_bits_nonzero | positive_product_overflows | negative_product_underflows;
            E::assert_eq(overflow, E::zero());

            // Return the product of `self` and `other` with the appropriate sign.
            Self::ternary(operands_same_sign, &product, &Self::zero().sub_wrapped(&product))
        } else {
            // Compute the product of `self` and `other`.
            let (product, carry) = Self::mul_with_carry(self, other);

            // For unsigned multiplication, check that none of the carry bits are set.
            let overflow = carry.iter().fold(Boolean::constant(false), |a, b| a | b);
            E::assert_eq(overflow, E::zero());

            // Return the product of `self` and `other`.
            product
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn MulChecked<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, I>);
    type OutputType = IntegerCircuitType<E, I>;

    fn count(case: &Self::Case) -> Count {
        let (lhs, rhs) = case;
        match lhs.is_constant() && rhs.is_constant() {
            true => Count::is(I::BITS, 0, 0, 0),
            false => {
                let mut total_count = Count::zero();
                if I::is_signed() {
                    // Determine the count and output type of `let (product, carry) = Self::mul_with_carry(&self.abs_wrapped(), &other.abs_wrapped());`.
                    total_count = total_count + count!(Self, AbsWrapped<Output = Self>, lhs);
                    let self_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, lhs.clone());

                    total_count = total_count + count!(Self, AbsWrapped<Output = Self>, rhs);
                    let other_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, rhs.clone());

                    let case = (self_abs_wrapped_type, other_abs_wrapped_type);
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
                            let output_type = output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);
                            (cummulative_count + count, output_type)
                        },
                    );
                    total_count = total_count + count;

                    // Determine the count and output type of `let operands_same_sign = &self.msb().is_equal(other.msb());`.
                    total_count = total_count + count!(Self, MSB<Boolean = Boolean<E>>, lhs);
                    let self_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, lhs.clone());

                    total_count = total_count + count!(Self, MSB<Boolean = Boolean<E>>, rhs);
                    let other_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, rhs.clone());

                    let case = (self_msb_type, other_msb_type);
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
                        let lower_product_bits_nonzero_not_type =
                            output_type!(Boolean<E>, Not<Output = Boolean<E>>, lower_product_bits_nonzero_type);

                        let case = (product_msb_type, lower_product_bits_nonzero_not_type);
                        total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                        let product_msb_or_not_lower_product_bits_nonzero_type =
                            output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

                        let case = (product_msb_not_type, product_msb_or_not_lower_product_bits_nonzero_type);
                        total_count = total_count + count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                        let negative_product_lt_or_eq_signed_min_type =
                            output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);

                        // Determine the count and output type of `!operands_same_sign & !negative_product_lt_or_eq_signed_min`.
                        total_count =
                            total_count + count!(Boolean<E>, Not<Output = Boolean<E>>, &operands_same_sign_type);
                        let operands_same_sign_not_type =
                            output_type!(Boolean<E>, Not<Output = Boolean<E>>, operands_same_sign_type.clone());

                        total_count = total_count
                            + count!(Boolean<E>, Not<Output = Boolean<E>>, &negative_product_lt_or_eq_signed_min_type);
                        let negative_product_lt_or_eq_signed_min_not_type = output_type!(
                            Boolean<E>,
                            Not<Output = Boolean<E>>,
                            negative_product_lt_or_eq_signed_min_type
                        );

                        let case = (operands_same_sign_not_type, negative_product_lt_or_eq_signed_min_not_type);
                        total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);

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

                    // Determine the cost of `E::assert_eq(overflow, E::zero());`.
                    match overflow_type.is_constant() {
                        true => (), // Do nothing.
                        false => total_count = total_count + Count::is(0, 0, 0, 1),
                    }

                    // Determine the count and output type of `Self::ternary(operands_same_sign, &product, &Self::zero().sub_wrapped(&product))`.
                    total_count = total_count + count!(Self, Zero<Boolean = Boolean<E>>, &());
                    let zero_type = output_type!(Self, Zero<Boolean = Boolean<E>>, ());

                    let case = (zero_type, product_type.clone());
                    total_count = total_count + count!(Self, SubWrapped<Self, Output = Self>, &case);
                    let zero_sub_product_type = output_type!(Self, SubWrapped<Self, Output = Self>, case);

                    let case = (operands_same_sign_type, product_type, zero_sub_product_type);
                    total_count = total_count + count!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, &case);
                } else {
                    // Determine the count and output type of `let (product, carry) = Self::mul_with_carry(self, other);`.
                    let case = (lhs.clone(), rhs.clone());
                    total_count =
                        total_count + count!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, &case);
                    let (_product_type, carry_type) =
                        output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, case);

                    // Determine the count and output type of `let overflow = carry.iter().fold(Boolean::constant(false), |a, b| a | b);`.
                    let (count, overflow_type) = carry_type.into_iter().fold(
                        (Count::zero(), CircuitType::from(Boolean::constant(false))),
                        |(cummulative_count, prev_type), next_type| {
                            let case = (prev_type, next_type);
                            let count = count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &case);
                            let output_type = output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, case);
                            (cummulative_count + count, output_type)
                        },
                    );
                    total_count = total_count + count;

                    // Determine the count and output type of `E::assert_eq(overflow, E::zero());`.
                    match overflow_type.is_constant() {
                        true => (), // Do nothing.
                        false => total_count = total_count + Count::is(0, 0, 0, 1),
                    }
                }
                total_count
            }
        }
    }

    // TODO: Overflow check.
    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs) = case;

        if I::is_signed() {
            // Determine the output type  of `let (product, carry) = Self::mul_with_carry(&self.abs_wrapped(), &other.abs_wrapped());`
            let self_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, lhs.clone());
            let other_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, rhs.clone());

            let case = (self_abs_wrapped_type, other_abs_wrapped_type);
            let (product_type, _carry_type) =
                output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, case);

            // Determine the output type of `let operands_same_sign = &self.msb().is_equal(other.msb());`.
            let self_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, lhs);
            let other_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, rhs);
            let operands_same_sign_type =
                output_type!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, (self_msb_type, other_msb_type));

            // Determine the output type of `Self::ternary(operands_same_sign, &product, &Self::zero().sub_wrapped(&product))`.
            let zero_type = output_type!(Self, Zero<Boolean = Boolean<E>>, ());
            let case = (zero_type, product_type.clone());
            let zero_sub_product_type = output_type!(Self, SubWrapped<Self, Output = Self>, case);

            let case = (operands_same_sign_type, product_type, zero_sub_product_type);

            output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case)
        } else {
            // Determine the output type of `let (product, carry) = Self::mul_with_carry(&result, self);`.
            let (product_type, _carry_type) =
                output_type!(Self, MulWithCarry<Product = Self, Carry = Vec<Boolean<E>>>, (lhs, rhs));

            // Return the product of `self` and `other`.
            product_type
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 32;

    fn check_mul<I: IntegerType + RefUnwindSafe>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        match first.checked_mul(&second) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.mul_checked(&b);
                assert_eq!(expected, candidate.eject_value());

                let case = (IntegerCircuitType::from(a), IntegerCircuitType::from(b));
                assert_count!(MulChecked(Integer<I>, Integer<I>) => Integer<I>, &case);
                assert_output_type!(MulChecked(Integer<I>, Integer<I>) => Integer<I>, case, candidate);
            }),
            None => match (mode_a, mode_b) {
                (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::mul_checked),
                _ => Circuit::scope(name, || {
                    let _candidate = a.mul_checked(&b);

                    let case = (IntegerCircuitType::from(a), IntegerCircuitType::from(b));
                    assert_count_fails!(MulChecked(Integer<I>, Integer<I>) => Integer<I>, &case);
                }),
            },
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            // TODO (@pranav) Uniform random sampling almost always produces arguments that result in an overflow.
            //  Is there a better method for sampling arguments?
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Mul: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, second, mode_a, mode_b);
            check_mul(&name, second, first, mode_a, mode_b); // Commute the operation.

            let name = format!("Double: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, I::one() + I::one(), mode_a, mode_b);
            check_mul(&name, I::one() + I::one(), first, mode_a, mode_b); // Commute the operation.

            let name = format!("Square: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, first, mode_a, mode_b);
        }

        // Check specific cases common to signed and unsigned integers.
        check_mul("1 * MAX", I::one(), I::MAX, mode_a, mode_b);
        check_mul("MAX * 1", I::MAX, I::one(), mode_a, mode_b);
        check_mul("1 * MIN", I::one(), I::MIN, mode_a, mode_b);
        check_mul("MIN * 1", I::MIN, I::one(), mode_a, mode_b);
        check_mul("0 * MAX", I::zero(), I::MAX, mode_a, mode_b);
        check_mul("MAX * 0", I::MAX, I::zero(), mode_a, mode_b);
        check_mul("0 * MIN", I::zero(), I::MIN, mode_a, mode_b);
        check_mul("MIN * 0", I::MIN, I::zero(), mode_a, mode_b);
        check_mul("1 * 1", I::one(), I::one(), mode_a, mode_b);

        // Check common overflow cases.
        check_mul("MAX * 2", I::MAX, I::one() + I::one(), mode_a, mode_b);
        check_mul("2 * MAX", I::one() + I::one(), I::MAX, mode_a, mode_b);

        // Check additional corner cases for signed integers.
        if I::is_signed() {
            check_mul("MAX * -1", I::MAX, I::zero() - I::one(), mode_a, mode_b);
            check_mul("-1 * MAX", I::zero() - I::one(), I::MAX, mode_a, mode_b);
            check_mul("MIN * -1", I::MIN, I::zero() - I::one(), mode_a, mode_b);
            check_mul("-1 * MIN", I::zero() - I::one(), I::MIN, mode_a, mode_b);
            check_mul("MIN * -2", I::MIN, I::zero() - I::one() - I::one(), mode_a, mode_b);
            check_mul("-2 * MIN", I::zero() - I::one() - I::one(), I::MIN, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Mul: ({} * {})", first, second);
                check_mul(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, times);
    test_integer_binary!(run_test, i16, times);
    test_integer_binary!(run_test, i32, times);
    test_integer_binary!(run_test, i64, times);
    test_integer_binary!(run_test, i128, times);

    test_integer_binary!(run_test, u8, times);
    test_integer_binary!(run_test, u16, times);
    test_integer_binary!(run_test, u32, times);
    test_integer_binary!(run_test, u64, times);
    test_integer_binary!(run_test, u128, times);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, times, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, times, exhaustive);
}
