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

impl<E: Environment, I: IntegerType> NegFlagged for Integer<E, I> {
    type Output = (Integer<E, I>, Boolean<E>);

    /// Performs the unary `-` operation, returning the result and a flag indicating whether the operation overflowed.
    fn neg_flagged(self) -> Self::Output {
        (&self).neg_flagged()
    }
}

impl<E: Environment, I: IntegerType> NegFlagged for &Integer<E, I> {
    type Output = (Integer<E, I>, Boolean<E>);

    /// Performs the unary `-` operation, returning the result and a flag indicating whether the operation overflowed.
    fn neg_flagged(self) -> Self::Output {
        match I::is_signed() {
            true => Integer::one().add_flagged(&!self),
            // Note: `halt` is necessary since negation is not defined for unsigned integers.
            false => E::halt("Attempted to negate an unsigned integer"),
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn NegFlagged<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            false => E::halt("Unsigned integers cannot be negated"),
            true => match case {
                Mode::Constant => Count::is(2 * I::BITS + 1, 0, 0, 0),
                _ => Count::is(I::BITS, 0, I::BITS + 2, I::BITS + 3),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn NegFlagged<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match case {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::UnwindSafe};

    const ITERATIONS: u64 = 128;

    fn check_neg<I: IntegerType + UnwindSafe + Neg<Output = I>>(
        name: &str,
        value: console::Integer<<Circuit as Environment>::Network, I>,
        mode: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode, value);

        // Check that the flagged implementation produces the correct result.
        let (expected_result, expected_flag) = value.overflowing_neg();
        Circuit::scope(name, || {
            let (candidate_result, candidate_flag) = (&a).neg_flagged();
            assert_eq!(expected_result, *candidate_result.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_result), candidate_result.eject_value());
            assert_count!(NegFlagged(Integer<I>) => Integer<I>, &mode);
            assert_output_mode!(NegFlagged(Integer<I>) => Integer<I>, &mode, candidate_result);
        });
        Circuit::reset();

        let (flagged_result, flag) = (&a).neg_flagged();

        // Check that the flagged implementation matches the standard implementation.
        match (flag.eject_value(), mode) {
            (true, Mode::Constant) => check_unary_operation_halts(a, Integer::neg),
            _ => {
                Circuit::scope(name, || {
                    let standard_result = &a.neg();
                    assert_eq!(flagged_result.eject_value(), standard_result.eject_value());
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

    fn run_test<I: IntegerType + UnwindSafe + Neg<Output = I>>(mode: Mode) {
        // Check the 0 case.
        check_neg::<I>(&format!("Neg: {} zero", mode), console::Integer::zero(), mode);
        // Check the 1 case.
        check_neg::<I>(&format!("Neg: {} one", mode), -console::Integer::one(), mode);
        // Check random values.
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let value = Uniform::rand(&mut rng);
            check_neg::<I>(&format!("Neg: {} {}", mode, i), value, mode);
        }
    }

    fn assert_unsigned_neg_halts<I: IntegerType + UnwindSafe>(mode: Mode) {
        let candidate = Integer::<Circuit, I>::new(mode, Uniform::rand(&mut TestRng::default()));
        let operation = std::panic::catch_unwind(|| candidate.neg());
        assert!(operation.is_err());
    }

    fn run_exhaustive_test<I: IntegerType + UnwindSafe + Neg<Output = I>>(mode: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for value in I::MIN..=I::MAX {
            let value = console::Integer::<_, I>::new(value);

            let name = format!("Neg: {}", mode);
            check_neg::<I>(&name, value, mode);
        }
    }

    test_integer_unary!(run_test, i8, neg);
    test_integer_unary!(run_test, i16, neg);
    test_integer_unary!(run_test, i32, neg);
    test_integer_unary!(run_test, i64, neg);
    test_integer_unary!(run_test, i128, neg);

    test_integer_unary!(assert_unsigned_neg_halts, u8, neg);
    test_integer_unary!(assert_unsigned_neg_halts, u16, neg);
    test_integer_unary!(assert_unsigned_neg_halts, u32, neg);
    test_integer_unary!(assert_unsigned_neg_halts, u64, neg);
    test_integer_unary!(assert_unsigned_neg_halts, u128, neg);

    test_integer_unary!(#[ignore], assert_unsigned_neg_halts, u8, neg, exhaustive);
    test_integer_unary!(#[ignore], run_exhaustive_test, i8, neg, exhaustive);
}
