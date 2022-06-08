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

impl<E: Environment, I: IntegerType> MulWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn mul_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the product and return the new constant.
            witness!(|self, other| console::Integer::new(self.wrapping_mul(&other)))
        } else {
            // Perform multiplication by decomposing it into operations on its upper and lower bits.
            // See this page for reference: https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            // Note: We follow the naming convention given in the `Basic Step` section of the cited page.
            // For integers with size less than 128, this algorithm saves approximately 0.5 * I::BITS
            // constraints compared to a field multiplication.
            let x_1 = Field::from_bits_le(&self.bits_le[(I::BITS as usize / 2)..]);
            let x_0 = Field::from_bits_le(&self.bits_le[..(I::BITS as usize / 2)]);
            let y_1 = Field::from_bits_le(&other.bits_le[(I::BITS as usize / 2)..]);
            let y_0 = Field::from_bits_le(&other.bits_le[..(I::BITS as usize / 2)]);

            let z_0 = &x_0 * &y_0;
            let z_1 = (&x_1 * &y_0) + (&x_0 * &y_1);

            let mut b_m_bits = vec![Boolean::constant(false); I::BITS as usize / 2];
            b_m_bits.push(Boolean::constant(true));

            let b_m = Field::from_bits_le(&b_m_bits);
            let z_0_plus_z_1 = &z_0 + (&z_1 * &b_m);

            let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS as usize + I::BITS as usize / 2 + 1);

            // Remove any carry bits.
            bits_le.truncate(I::BITS as usize);

            // Return the product of `self` and `other`, without the carry bits.
            Integer { bits_le, phantom: Default::default() }
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn MulWrapped<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            (Mode::Constant, _) | (_, Mode::Constant) => {
                Count::is(0, 0, I::BITS + (I::BITS / 2) + 1, I::BITS + (I::BITS / 2) + 2)
            }
            (_, _) => Count::is(0, 0, I::BITS + (I::BITS / 2) + 4, I::BITS + (I::BITS / 2) + 5),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn MulWrapped<Integer<E, I>, Output = Integer<E, I>>>
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

    use core::ops::RangeInclusive;

    const ITERATIONS: u64 = 32;

    fn check_mul<I: IntegerType>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let expected = first.wrapping_mul(&second);
        Circuit::scope(name, || {
            let candidate = a.mul_wrapped(&b);
            assert_eq!(expected, *candidate.eject_value());
            assert_eq!(console::Integer::new(expected), candidate.eject_value());
            assert_count!(MulWrapped(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
            assert_output_mode!(MulWrapped(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_a: Mode, mode_b: Mode) {
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

    fn run_exhaustive_test<I: IntegerType>(mode_a: Mode, mode_b: Mode)
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
