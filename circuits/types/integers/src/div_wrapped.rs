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

impl<E: Environment, I: IntegerType> DivWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn div_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Halt on division by zero as there is no sound way to perform
        // this operation.
        if other.eject_value().is_zero() {
            E::halt("Division by zero error")
        }

        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the quotient and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_div(&other.eject_value()))
        } else if I::is_signed() {
            // Divide the absolute value of `self` and `other` in the base field.
            let unsigned_dividend = self.abs_wrapped().cast_as_dual();
            let unsigned_divisor = other.abs_wrapped().cast_as_dual();
            let unsigned_quotient = unsigned_dividend.div_wrapped(&unsigned_divisor);

            // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
            //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
            let signed_quotient = Self { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
            let operands_same_sign = &self.msb().is_equal(other.msb());
            let signed_quotient =
                Self::ternary(operands_same_sign, &signed_quotient, &Self::zero().sub_wrapped(&signed_quotient));

            // Signed integer division wraps when the dividend is I::MIN and the divisor is -1.
            let min = Self::constant(I::MIN);
            let neg_one = Self::constant(I::zero() - I::one());
            let overflows = self.is_equal(&min) & other.is_equal(&neg_one);
            Self::ternary(&overflows, &min, &signed_quotient)
        } else {
            // Eject the dividend and divisor, to compute the quotient as a witness.
            let dividend_value = self.eject_value();
            let divisor_value = other.eject_value();

            // Overflow is not possible for unsigned integers so we use wrapping operations.
            let quotient = Integer::new(Mode::Private, dividend_value.wrapping_div(&divisor_value));
            let remainder = Integer::new(Mode::Private, dividend_value.wrapping_rem(&divisor_value));

            // Ensure that Euclidean division holds for these values in the base field.
            E::assert_eq(self.to_field(), quotient.to_field() * other.to_field() + remainder.to_field());

            // Return the quotient of `self` and `other`.
            quotient
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn DivWrapped<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, I>);
    type OutputType = IntegerCircuitType<E, I>;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => {
                let (lhs, rhs) = case;

                match lhs.is_constant() && rhs.is_constant() {
                    true => Count::is(I::BITS, 0, 0, 0),
                    false => {
                        let mut total_count = Count::zero();

                        // Determine the cost and output type of `let unsigned_dividend = self.abs_wrapped().cast_as_dual();`
                        total_count = total_count + count!(Self, AbsWrapped<Output = Self>, &lhs);
                        let self_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, lhs.clone());
                        let unsigned_dividend_type = IntegerCircuitType::<E, I::Dual> {
                            bits_le: self_abs_wrapped_type.bits_le,
                            phantom: Default::default(),
                        };

                        // Determine the cost and output type of `let unsigned_divisor = other.abs_wrapped().cast_as_dual();`
                        total_count = total_count + count!(Self, AbsWrapped<Output = Self>, &rhs);
                        let other_abs_wrapped_type = output_type!(Self, AbsWrapped<Output = Self>, rhs.clone());
                        let unsigned_divisor_type = IntegerCircuitType::<E, I::Dual> {
                            bits_le: other_abs_wrapped_type.bits_le,
                            phantom: Default::default(),
                        };

                        // Determine the cost and output type of `let unsigned_quotient = unsigned_dividend.div_wrapped(unsigned_divisor);`
                        let case = (unsigned_dividend_type, unsigned_divisor_type);
                        total_count = total_count
                            + count!(Integer<E, I::Dual>, DivWrapped<Integer<E, I::Dual>, Output = Integer<E, I::Dual>>, &case);
                        let unsigned_quotient_type = output_type!(Integer<E, I::Dual>, DivWrapped<Integer<E, I::Dual>, Output = Integer<E, I::Dual>>, case);

                        // Determine the cost and output type of `Self { bits_le: unsigned_quotient_type.bits_le, phantom: Default::default() }`
                        let signed_quotient_type = IntegerCircuitType::<E, I> {
                            bits_le: unsigned_quotient_type.bits_le,
                            phantom: Default::default(),
                        };

                        // Determine the cost and output type of `let operands_same_sing = &self.msb().is_equal(other.msb());`
                        total_count = total_count
                            + count!(Self, MSB<Boolean = Boolean<E>>, &lhs)
                            + count!(Self, MSB<Boolean = Boolean<E>>, &rhs);
                        let self_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, lhs.clone());
                        let other_msb_type = output_type!(Self, MSB<Boolean = Boolean<E>>, rhs.clone());

                        let case = (self_msb_type, other_msb_type);
                        total_count = total_count + count!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, &case);
                        let operands_same_sign_type =
                            output_type!(Boolean<E>, Equal<Boolean<E>, Output = Boolean<E>>, case);

                        // Determine the cost and output type of `let signed_quotient =
                        //                     Self::ternary(operands_same_sign, &signed_quotient, &Self::zero().sub_wrapped(&signed_quotient));`
                        total_count = total_count + count!(Self, Zero<Boolean = Boolean<E>>, &());
                        let zero_type = output_type!(Self, Zero<Boolean = Boolean<E>>, ());

                        let case = (zero_type, signed_quotient_type.clone());
                        total_count = total_count + count!(Self, SubWrapped<Self, Output = Self>, &case);
                        let second_type = output_type!(Self, SubWrapped<Self, Output = Self>, case);

                        let case = (operands_same_sign_type, signed_quotient_type, second_type);
                        total_count = total_count + count!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, &case);
                        let signed_quotient_type =
                            output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case);

                        // Determine the cost and output type of `let overflows = self.is_equal(&min) & other.is_equal(&neg_one);`.
                        // `Self::constant(I::MIN)` produces I::BITS constant bits.
                        total_count = total_count + Count::is(I::BITS, 0, 0, 0);
                        let min_type = IntegerCircuitType::from(Self::constant(I::MIN));

                        let case = (lhs.clone(), min_type.clone());
                        total_count = total_count + count!(Self, Equal<Self, Output = Boolean<E>>, &case);
                        let self_is_equal_min_type = output_type!(Self, Equal<Self, Output = Boolean<E>>, case);

                        // `Self::constant(I::zero() - I::one())` produces I::BITS constant bits.
                        total_count = total_count + Count::is(I::BITS, 0, 0, 0);
                        let neg_one_type = IntegerCircuitType::from(Self::constant(I::zero() - I::one()));

                        let case = (rhs.clone(), neg_one_type);
                        total_count = total_count + count!(Self, Equal<Self, Output = Boolean<E>>, &case);
                        let other_is_equal_neg_one_type = output_type!(Self, Equal<Self, Output = Boolean<E>>, case);

                        let case = (self_is_equal_min_type, other_is_equal_neg_one_type);
                        total_count = total_count + count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
                        let overflows_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

                        // Determine the cost and output type of `Self::ternary(overflows, &min, &signed_quotient)`
                        let case = (overflows_type, min_type, signed_quotient_type);
                        total_count = total_count + count!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, &case);

                        total_count
                    }
                }
            }
            false => match (case.0.eject_mode(), case.1.eject_mode()) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (_, Mode::Constant) => Count::is(0, 0, 2 * I::BITS, (2 * I::BITS) + 1),
                (Mode::Constant, _) | (_, _) => Count::is(0, 0, (2 * I::BITS) + 1, (2 * I::BITS) + 2),
            },
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs) = case;
        match lhs.is_constant() && rhs.is_constant() {
            true => IntegerCircuitType::from(lhs.circuit().div_wrapped(&rhs.circuit())),
            false => IntegerCircuitType::private(),
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

    fn check_div<I: IntegerType + RefUnwindSafe>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        if second == I::zero() {
            check_operation_halts(&a, &b, Integer::div_wrapped);
        } else {
            let expected = first.wrapping_div(&second);
            Circuit::scope(name, || {
                let candidate = a.div_wrapped(&b);
                assert_eq!(expected, candidate.eject_value());

                let case = (IntegerCircuitType::from(a), IntegerCircuitType::from(b));
                assert_count!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, &case);
                assert_output_type!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, case, candidate);
            })
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for _ in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Div: {} / {}", first, second);
            check_div(&name, first, second, mode_a, mode_b);

            let name = format!("Div by One: {} / {}", first, I::one());
            check_div(&name, first, I::one(), mode_a, mode_b);

            let name = format!("Div by Self: {} / {}", first, first);
            check_div(&name, first, first, mode_a, mode_b);

            let name = format!("Div by Zero: {} / {}", first, I::zero());
            check_div(&name, first, I::zero(), mode_a, mode_b);
        }

        // Check standard division properties and corner cases.
        check_div("MAX / 1", I::MAX, I::one(), mode_a, mode_b);
        check_div("MIN / 1", I::MIN, I::one(), mode_a, mode_b);
        check_div("1 / 1", I::one(), I::one(), mode_a, mode_b);
        check_div("0 / 1", I::zero(), I::one(), mode_a, mode_b);
        check_div("MAX / 0", I::MAX, I::zero(), mode_a, mode_b);
        check_div("MIN / 0", I::MIN, I::zero(), mode_a, mode_b);
        check_div("1 / 0", I::one(), I::zero(), mode_a, mode_b);
        check_div("0 / 0", I::zero(), I::zero(), mode_a, mode_b);

        // Check some additional corner cases for signed integer division.
        if I::is_signed() {
            check_div("MAX / -1", I::MAX, I::zero() - I::one(), mode_a, mode_b);
            check_div("MIN / -1", I::MIN, I::zero() - I::one(), mode_a, mode_b);
            check_div("1 / -1", I::one(), I::zero() - I::one(), mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Div: ({} / {})", first, second);
                check_div(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, div);
    test_integer_binary!(run_test, i16, div);
    test_integer_binary!(run_test, i32, div);
    test_integer_binary!(run_test, i64, div);
    test_integer_binary!(run_test, i128, div);

    test_integer_binary!(run_test, u8, div);
    test_integer_binary!(run_test, u16, div);
    test_integer_binary!(run_test, u32, div);
    test_integer_binary!(run_test, u64, div);
    test_integer_binary!(run_test, u128, div);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, div, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, div, exhaustive);
}
