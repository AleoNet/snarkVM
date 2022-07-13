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
                Some(value) => Integer::new(Mode::Constant, console::Integer::new(value)),
                None => E::halt("Constant shifted by constant exceeds the allowed bitwidth."),
            }
        } else {
            // Determine the index where the first upper bit of the RHS must be zero.
            // There is at least one trailing zero, as I::BITS = 8, 16, 32, 64, or 128.
            let trailing_zeros_index = I::BITS.trailing_zeros() as usize;

            // Determine if any of the upper bits of the RHS are nonzero.
            let is_nonzero = rhs.bits_le[trailing_zeros_index..].iter().fold(Boolean::constant(false), |a, b| a | b);

            // Ensure the upper bits of the RHS are zero.
            E::assert(!is_nonzero);

            // Perform a wrapping shift left.
            self.shl_wrapped(rhs)
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn Shl<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        <Self as Metrics<dyn DivChecked<Integer<E, I>, Output = Integer<E, I>>>>::count(case)
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Shl<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        <Self as OutputMode<dyn DivChecked<Integer<E, I>, Output = Integer<E, I>>>>::output_mode(case)
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metrics<dyn ShlChecked<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        // A quick hack that matches `(u8 -> 0, u16 -> 1, u32 -> 2, u64 -> 3, u128 -> 4)`.
        let index = |num_bits: u64| match [8, 16, 32, 64, 128].iter().position(|&bits| bits == num_bits) {
            Some(index) => index as u64,
            None => E::halt(format!("Integer of {num_bits} bits is not supported")),
        };

        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            (_, Mode::Constant) => Count::is(0, 0, 0, 0),
            (Mode::Constant, _) | (_, _) => {
                let wrapped_count = count!(Integer<E, I>, ShlWrapped<Integer<E, M>, Output=Integer<E, I>>, case);
                wrapped_count + Count::is(0, 0, M::BITS - 4 - index(I::BITS), M::BITS - 3 - index(I::BITS))
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> OutputMode<dyn ShlChecked<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (mode_a, Mode::Constant) => mode_a,
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

    fn check_shl<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, M>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        match first.checked_shl(second.to_u32().unwrap()) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.shl_checked(&b);
                assert_eq!(expected, *candidate.eject_value());
                assert_eq!(console::Integer::new(expected), candidate.eject_value());
                assert_count!(ShlChecked(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b));
                assert_output_mode!(ShlChecked(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b), candidate);
            }),
            None => match (mode_a, mode_b) {
                (_, Mode::Constant) => check_operation_halts(&a, &b, Integer::shl_checked),
                _ => Circuit::scope(name, || {
                    let _candidate = a.shl_checked(&b);
                    assert_count_fails!(ShlChecked(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b));
                }),
            },
        };
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let name = format!("Shl: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, second, mode_a, mode_b);

            // Check that shift left by one is computed correctly.
            let name = format!("Double: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::one(), mode_a, mode_b);

            // Check that shift left by two is computed correctly.
            let name = format!("Quadruple: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::one() + console::Integer::one(), mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let first = console::Integer::<_, I>::new(first);
                let second = console::Integer::<_, M>::new(second);

                let name = format!("Shl: ({} << {})", first, second);
                check_shl::<I, M>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, u8, shl);
    test_integer_binary!(run_test, i8, u16, shl);
    test_integer_binary!(run_test, i8, u32, shl);

    test_integer_binary!(run_test, i16, u8, shl);
    test_integer_binary!(run_test, i16, u16, shl);
    test_integer_binary!(run_test, i16, u32, shl);

    test_integer_binary!(run_test, i32, u8, shl);
    test_integer_binary!(run_test, i32, u16, shl);
    test_integer_binary!(run_test, i32, u32, shl);

    test_integer_binary!(run_test, i64, u8, shl);
    test_integer_binary!(run_test, i64, u16, shl);
    test_integer_binary!(run_test, i64, u32, shl);

    test_integer_binary!(run_test, i128, u8, shl);
    test_integer_binary!(run_test, i128, u16, shl);
    test_integer_binary!(run_test, i128, u32, shl);

    test_integer_binary!(run_test, u8, u8, shl);
    test_integer_binary!(run_test, u8, u16, shl);
    test_integer_binary!(run_test, u8, u32, shl);

    test_integer_binary!(run_test, u16, u8, shl);
    test_integer_binary!(run_test, u16, u16, shl);
    test_integer_binary!(run_test, u16, u32, shl);

    test_integer_binary!(run_test, u32, u8, shl);
    test_integer_binary!(run_test, u32, u16, shl);
    test_integer_binary!(run_test, u32, u32, shl);

    test_integer_binary!(run_test, u64, u8, shl);
    test_integer_binary!(run_test, u64, u16, shl);
    test_integer_binary!(run_test, u64, u32, shl);

    test_integer_binary!(run_test, u128, u8, shl);
    test_integer_binary!(run_test, u128, u16, shl);
    test_integer_binary!(run_test, u128, u32, shl);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, u8, shl, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, u8, shl, exhaustive);
}
