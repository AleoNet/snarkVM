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

impl<E: Environment, I: IntegerType> Metrics<dyn Mul<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        <Self as Metrics<dyn DivChecked<Integer<E, I>, Output = Integer<E, I>>>>::count(case)
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Mul<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        <Self as OutputMode<dyn DivChecked<Integer<E, I>, Output = Integer<E, I>>>>::output_mode(case)
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
                Some(value) => Integer::new(Mode::Constant, console::Integer::new(value)),
                None => E::halt("Integer overflow on multiplication of two constants"),
            }
        } else if I::is_signed() {
            // Multiply the absolute value of `self` and `other` in the base field.
            // Note that it is safe to use abs_wrapped since we want Integer::MIN to be interpreted as an unsigned number.
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

impl<E: Environment, I: IntegerType> Integer<E, I> {
    /// Multiply the integer bits of `this` and `that` in the base field.
    #[inline]
    pub(super) fn mul_with_carry(this: &Integer<E, I>, that: &Integer<E, I>) -> (Integer<E, I>, Vec<Boolean<E>>) {
        // Case 1 - 2 integers fit in 1 field element (u8, u16, u32, u64, i8, i16, i32, i64).
        if 2 * I::BITS < (E::BaseField::size_in_bits() - 1) as u64 {
            // Instead of multiplying the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and multiplied, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let product = (this.to_field() * that.to_field()).to_lower_bits_le(2 * I::BITS as usize);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = product.split_at(I::BITS as usize);

            // Return the product of `self` and `other`, along with the carry bits.
            (Integer::from_bits_le(bits_le), carry.to_vec())
        }
        // Case 2 - 1.5 integers fit in 1 field element (u128, i128).
        else if (I::BITS + I::BITS / 2) < (E::BaseField::size_in_bits() - 1) as u64 {
            // Perform multiplication by decomposing it into operations on its upper and lower bits.
            // See this page for reference: https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            // Note: We follow the naming convention given in the `Basic Step` section of the cited page.
            let x_1 = Field::from_bits_le(&this.bits_le[(I::BITS as usize / 2)..]);
            let x_0 = Field::from_bits_le(&this.bits_le[..(I::BITS as usize / 2)]);
            let y_1 = Field::from_bits_le(&that.bits_le[(I::BITS as usize / 2)..]);
            let y_0 = Field::from_bits_le(&that.bits_le[..(I::BITS as usize / 2)]);

            let z_0 = &x_0 * &y_0;
            let z_1 = (&x_1 * &y_0) + (&x_0 * &y_1);

            let mut b_m_bits = vec![Boolean::constant(false); I::BITS as usize / 2];
            b_m_bits.push(Boolean::constant(true));

            let b_m = Field::from_bits_le(&b_m_bits);
            let z_0_plus_z_1 = &z_0 + (&z_1 * &b_m);

            let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS as usize + I::BITS as usize / 2 + 1);

            let z_2 = &x_1 * &y_1;
            bits_le.append(&mut z_2.to_lower_bits_le(I::BITS as usize));

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = bits_le.split_at(I::BITS as usize);

            // Return the product of `self` and `other`, along with the carry bits.
            (Integer::from_bits_le(bits_le), carry.to_vec())
        } else {
            E::halt(format!("Multiplication of integers of size {} is not supported", I::BITS))
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn MulChecked<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        // Case 1 - 2 integers fit in 1 field element (u8, u16, u32, u64, i8, i16, i32, i64).
        if 2 * I::BITS < (E::BaseField::size_in_bits() - 1) as u64 {
            match I::is_signed() {
                // Signed case
                true => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => {
                        Count::is(4 * I::BITS, 0, (8 * I::BITS) + 5, (8 * I::BITS) + 9)
                    }
                    (_, _) => Count::is(3 * I::BITS, 0, (10 * I::BITS) + 8, (10 * I::BITS) + 13),
                },
                // Unsigned case
                false => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => Count::is(0, 0, (3 * I::BITS) - 1, (3 * I::BITS) + 1),
                    (_, _) => Count::is(0, 0, 3 * I::BITS, (3 * I::BITS) + 2),
                },
            }
        }
        // Case 2 - 1.5 integers fit in 1 field element (u128, i128).
        else if (I::BITS + I::BITS / 2) < (E::BaseField::size_in_bits() - 1) as u64 {
            match I::is_signed() {
                // Signed case
                true => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => {
                        Count::is(4 * I::BITS, 0, (9 * I::BITS) + 7, (9 * I::BITS) + 12)
                    }
                    (_, _) => Count::is(3 * I::BITS, 0, (11 * I::BITS) + 13, (11 * I::BITS) + 19),
                },
                // Unsigned case
                false => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => Count::is(0, 0, (4 * I::BITS) + 1, (4 * I::BITS) + 4),
                    (_, _) => Count::is(0, 0, (4 * I::BITS) + 5, (4 * I::BITS) + 8),
                },
            }
        } else {
            E::halt(format!("Multiplication of integers of size {} is not supported", I::BITS))
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn MulChecked<Integer<E, I>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 32;

    fn check_mul<I: IntegerType + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        match first.checked_mul(&second) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.mul_checked(&b);
                assert_eq!(expected, *candidate.eject_value());
                assert_eq!(console::Integer::new(expected), candidate.eject_value());
                assert_count!(MulChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
                assert_output_mode!(MulChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate);
            }),
            None => match (mode_a, mode_b) {
                (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::mul_checked),
                _ => Circuit::scope(name, || {
                    let _candidate = a.mul_checked(&b);
                    assert_count_fails!(MulChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
                }),
            },
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            // TODO (@pranav) Uniform random sampling almost always produces arguments that result in an overflow.
            //  Is there a better method for sampling arguments?
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let name = format!("Mul: {} * {} {}", mode_a, mode_b, i);
            check_mul::<I>(&name, first, second, mode_a, mode_b);
            check_mul::<I>(&name, second, first, mode_a, mode_b); // Commute the operation.

            let name = format!("Double: {} * {} {}", mode_a, mode_b, i);
            check_mul::<I>(&name, first, console::Integer::one() + console::Integer::one(), mode_a, mode_b);
            check_mul::<I>(&name, console::Integer::one() + console::Integer::one(), first, mode_a, mode_b); // Commute the operation.

            let name = format!("Square: {} * {} {}", mode_a, mode_b, i);
            check_mul::<I>(&name, first, first, mode_a, mode_b);
        }

        // Check specific cases common to signed and unsigned integers.
        check_mul::<I>("1 * MAX", console::Integer::one(), console::Integer::MAX, mode_a, mode_b);
        check_mul::<I>("MAX * 1", console::Integer::MAX, console::Integer::one(), mode_a, mode_b);
        check_mul::<I>("1 * MIN", console::Integer::one(), console::Integer::MIN, mode_a, mode_b);
        check_mul::<I>("MIN * 1", console::Integer::MIN, console::Integer::one(), mode_a, mode_b);
        check_mul::<I>("0 * MAX", console::Integer::zero(), console::Integer::MAX, mode_a, mode_b);
        check_mul::<I>("MAX * 0", console::Integer::MAX, console::Integer::zero(), mode_a, mode_b);
        check_mul::<I>("0 * MIN", console::Integer::zero(), console::Integer::MIN, mode_a, mode_b);
        check_mul::<I>("MIN * 0", console::Integer::MIN, console::Integer::zero(), mode_a, mode_b);
        check_mul::<I>("1 * 1", console::Integer::one(), console::Integer::one(), mode_a, mode_b);

        // Check common overflow cases.
        check_mul::<I>(
            "MAX * 2",
            console::Integer::MAX,
            console::Integer::one() + console::Integer::one(),
            mode_a,
            mode_b,
        );
        check_mul::<I>(
            "2 * MAX",
            console::Integer::one() + console::Integer::one(),
            console::Integer::MAX,
            mode_a,
            mode_b,
        );

        // Check additional corner cases for signed integers.
        if I::is_signed() {
            check_mul::<I>("MAX * -1", console::Integer::MAX, -console::Integer::one(), mode_a, mode_b);
            check_mul::<I>("-1 * MAX", -console::Integer::one(), console::Integer::MAX, mode_a, mode_b);
            check_mul::<I>("MIN * -1", console::Integer::MIN, -console::Integer::one(), mode_a, mode_b);
            check_mul::<I>("-1 * MIN", -console::Integer::one(), console::Integer::MIN, mode_a, mode_b);
            check_mul::<I>(
                "MIN * -2",
                console::Integer::MIN,
                -console::Integer::one() - console::Integer::one(),
                mode_a,
                mode_b,
            );
            check_mul::<I>(
                "-2 * MIN",
                -console::Integer::one() - console::Integer::one(),
                console::Integer::MIN,
                mode_a,
                mode_b,
            );
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let first = console::Integer::<_, I>::new(first);
                let second = console::Integer::<_, I>::new(second);

                let name = format!("Mul: ({} * {})", first, second);
                check_mul::<I>(&name, first, second, mode_a, mode_b);
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
