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

impl<E: Environment, I: IntegerType, M: Magnitude> ShlFlagged<Integer<E, M>> for Integer<E, I> {
    type Output = (Self, Boolean<E>);

    #[inline]
    fn shl_flagged(&self, rhs: &Integer<E, M>) -> Self::Output {
        let two = Self::one() + Self::one();
        match I::is_signed() {
            true => {
                // Compute 2 ^ `lhs` as unsigned integer of the size I::BITS.
                // This is necessary to avoid a spurious overflow when `rhs` is I::BITS - 1.
                // For example, 2i8 ^ 7i8 overflows, however -1i8 << 7i8 ==> -1i8 * 2i8 ^ 7i8 ==> -128i8, which is a valid i8 value.
                let unsigned_two = two.cast_as_dual();
                // Note that `pow_checked` is used to enforce that `rhs` < I::BITS.
                let (unsigned_factor, pow_flag) = unsigned_two.pow_flagged(rhs);
                // For all values of `rhs` such that `rhs` < I::BITS,
                //  - if `rhs` == I::BITS - 1, `signed_factor` == I::MIN,
                //  - otherwise, `signed_factor` is the same as `unsigned_factor`.
                let signed_factor = Self { bits_le: unsigned_factor.bits_le, phantom: Default::default() };

                // If `signed_factor` is I::MIN, then negate `self` in order to balance the sign of I::MIN.
                let signed_factor_is_min = &signed_factor.is_equal(&Self::constant(console::Integer::MIN));
                // - If `signed_factor` is I::MIN,
                //     - and `self` is zero or I::MIN, then `lhs` is equal to `self`.
                //     - otherwise, `lhs` is equal to `-self`.
                // - Otherwise, `lhs` is equal to `self`.
                let lhs = Self::ternary(signed_factor_is_min, &Self::zero().sub_wrapped(self), self);

                // Compute `lhs` * `factor`, which is equivalent to `lhs` * 2 ^ `rhs`.
                let (result, mul_flag) = lhs.mul_flagged(&signed_factor);
                (result, pow_flag | mul_flag)
            }
            // Compute `lhs` * 2 ^ `rhs`.
            false => {
                let (pow_result, pow_flag) = two.pow_flagged(rhs);
                println!("pow_result: {:?}, pow_flag: {:?}", pow_result, pow_flag);
                let (result, mul_flag) = self.mul_flagged(&pow_result);
                println!("result: {:?}, mul_lag: {:?}", result, mul_flag);
                (result, pow_flag | mul_flag)
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metrics<dyn ShlFlagged<Integer<E, M>, Output = Integer<E, I>>>
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
                let wrapped_count = count!(Integer<E, I>, ShlFlagged<Integer<E, M>, Output=Integer<E, I>>, case);
                wrapped_count + Count::is(0, 0, M::BITS - 4 - index(I::BITS), M::BITS - 3 - index(I::BITS))
            }
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> OutputMode<dyn ShlFlagged<Integer<E, M>, Output = Integer<E, I>>>
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

        // Check that the flagged implementation produces the correct result.
        let (expected_result, expected_flag) = first.overflowing_shl(&second.to_u32().unwrap());
        println!("{}: {} << {} = {}, flag: {}", name, first, second, expected_result, expected_flag);
        Circuit::scope(name, || {
            let (candidate_result, candidate_flag) = a.shl_flagged(&b);
            assert_eq!(expected_result, *candidate_result.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_result), candidate_result.eject_value());
            assert_count!(ShlFlagged(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b));
            assert_output_mode!(ShlFlagged(Integer<I>, Integer<M>) => Integer<I>, &(mode_a, mode_b), candidate_result);
        });
        Circuit::reset();

        let (flagged_result, flag) = (&a).shl_flagged(&b);

        // Check that the flagged implementation matches wrapped implementation.
        let wrapped_result = (&a).shl_wrapped(&b);
        assert_eq!(flagged_result.eject_value(), wrapped_result.eject_value());

        // Check that the flagged implementation matches the checked implementation.
        match (flag.eject_value(), mode_a, mode_b) {
            // If the flag is set and the mode is constant, the checked implementation should halt.
            (true, Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::shl_checked),
            _ => {
                Circuit::scope(name, || {
                    let checked_result = a.shl_checked(&b);
                    assert_eq!(flagged_result.eject_value(), checked_result.eject_value());
                    match flag.eject_value() {
                        // If the flag is set, the circuit should not be satisfied.
                        true => assert!(!Circuit::is_satisfied_in_scope()),
                        // If the flag is not set, the circuit should be satisfied.
                        false => assert!(Circuit::is_satisfied_in_scope()),
                    }
                });
                Circuit::reset();
            }
        }
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe + TryFrom<u64>>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("Shl: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, second, mode_a, mode_b);

            // Check that shift left by zero is computed correctly.
            let name = format!("Identity: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::zero(), mode_a, mode_b);

            // Check that shift left by one is computed correctly.
            let name = format!("Double: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::one(), mode_a, mode_b);

            // Check that shift left by two is computed correctly.
            let name = format!("Quadruple: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, first, console::Integer::one() + console::Integer::one(), mode_a, mode_b);

            // Check that zero shifted left by `second` is computed correctly.
            let name = format!("Zero: {} << {} {}", mode_a, mode_b, i);
            check_shl::<I, M>(&name, console::Integer::zero(), second, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe + TryFrom<u64>>(
        mode_a: Mode,
        mode_b: Mode,
    ) where
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
