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

impl<E: Environment, I: IntegerType> ModChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn mod_checked(&self, other: &Integer<E, I>) -> Self::Output {
        match I::is_signed() {
            true => E::halt("Attempted to take the modulus of a signed integer."),
            false => self.rem_checked(other),
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn ModChecked<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(2 * I::BITS, 0, 0, 0),
                (Mode::Constant, _) | (_, Mode::Constant) => {
                    Count::less_than(9 * I::BITS, 0, (8 * I::BITS) + 2, (8 * I::BITS) + 12)
                }
                (_, _) => Count::is(8 * I::BITS, 0, (10 * I::BITS) + 15, (10 * I::BITS) + 27),
            },
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(2 * I::BITS, 0, 0, 0),
                (_, Mode::Constant) => Count::is(2 * I::BITS, 0, (3 * I::BITS) + 1, (3 * I::BITS) + 4),
                (Mode::Constant, _) | (_, _) => Count::is(2 * I::BITS, 0, (3 * I::BITS) + 4, (3 * I::BITS) + 9),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn ModChecked<Integer<E, I>, Output = Integer<E, I>>>
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

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 32;

    fn check_mod<I: IntegerType + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);

        match I::is_signed() {
            true => check_operation_halts(&a, &b, Integer::mod_checked),
            false => {
                if second == console::Integer::zero() {
                    match mode_b {
                        Mode::Constant => check_operation_halts(&a, &b, Integer::mod_checked),
                        _ => Circuit::scope(name, || {
                            let _candidate = a.mod_checked(&b);
                            // assert_count_fails!(ModChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
                            assert!(!Circuit::is_satisfied_in_scope(), "(!is_satisfied_in_scope)");
                        }),
                    }
                } else {
                    match first.checked_mod(&second) {
                        Some(expected) => Circuit::scope(name, || {
                            let candidate = a.mod_checked(&b);
                            assert_eq!(expected, *candidate.eject_value());
                            assert_eq!(console::Integer::new(expected), candidate.eject_value());
                            // assert_count!(ModChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
                            // assert_output_mode!(ModChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate);
                            assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
                        }),
                        None => match (mode_a, mode_b) {
                            (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::mod_checked),
                            _ => Circuit::scope(name, || {
                                let _candidate = a.mod_checked(&b);
                                // assert_count_fails!(ModChecked(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
                                assert!(!Circuit::is_satisfied_in_scope(), "(!is_satisfied_in_scope)");
                            }),
                        },
                    }
                }
            }
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for _ in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let name = format!("Mod: {} MOD {}", first, second);
            check_mod::<I>(&name, first, second, mode_a, mode_b);

            let name = format!("Mod by One: {} MOD 1", first);
            check_mod::<I>(&name, first, console::Integer::one(), mode_a, mode_b);

            let name = format!("Mod by Self: {} MOD {}", first, first);
            check_mod::<I>(&name, first, first, mode_a, mode_b);

            let name = format!("Mod by Zero: {} MOD 0", first);
            check_mod::<I>(&name, first, console::Integer::zero(), mode_a, mode_b);
        }

        // Check standard properties and corner cases.
        check_mod::<I>("MAX MOD 1", console::Integer::MAX, console::Integer::one(), mode_a, mode_b);
        check_mod::<I>("MIN MOD 1", console::Integer::MIN, console::Integer::one(), mode_a, mode_b);
        check_mod::<I>("1 MOD 1", console::Integer::one(), console::Integer::one(), mode_a, mode_b);
        check_mod::<I>("0 MOD 1", console::Integer::zero(), console::Integer::one(), mode_a, mode_b);
        check_mod::<I>("MAX MOD 0", console::Integer::MAX, console::Integer::zero(), mode_a, mode_b);
        check_mod::<I>("MIN MOD 0", console::Integer::MIN, console::Integer::zero(), mode_a, mode_b);
        check_mod::<I>("1 MOD 0", console::Integer::one(), console::Integer::zero(), mode_a, mode_b);
        check_mod::<I>("0 MOD 0", console::Integer::zero(), console::Integer::zero(), mode_a, mode_b);

        // Check some additional corner cases for signed integers.
        if I::is_signed() {
            check_mod::<I>("MAX MOD -1", console::Integer::MAX, -console::Integer::one(), mode_a, mode_b);
            check_mod::<I>("MIN MOD -1", console::Integer::MIN, -console::Integer::one(), mode_a, mode_b);
            check_mod::<I>("1 MOD -1", console::Integer::one(), -console::Integer::one(), mode_a, mode_b);
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

                let name = format!("Mod: ({} MOD {})", first, second);
                check_mod::<I>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, mod);
    test_integer_binary!(run_test, i16, mod);
    test_integer_binary!(run_test, i32, mod);
    test_integer_binary!(run_test, i64, mod);
    test_integer_binary!(run_test, i128, mod);

    test_integer_binary!(run_test, u8, mod);
    test_integer_binary!(run_test, u16, mod);
    test_integer_binary!(run_test, u32, mod);
    test_integer_binary!(run_test, u64, mod);
    test_integer_binary!(run_test, u128, mod);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, mod, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, mod, exhaustive);
}
