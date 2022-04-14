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

impl<E: Environment, I: IntegerType> Neg for Integer<E, I> {
    type Output = Integer<E, I>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

impl<E: Environment, I: IntegerType> Neg for &Integer<E, I> {
    type Output = Integer<E, I>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        match I::is_signed() {
            // Note: This addition must be checked as `-I::MIN` is an invalid operation.
            true => Integer::one().add_checked(&!self),
            false => E::halt("Attempted to negate an unsigned integer"),
        }
    }
}

impl<E: Environment, I: IntegerType> Count<dyn Neg<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn count(input: &Self::Case) -> CircuitCount {
        match I::is_signed() {
            false => E::halt("Unsigned integers cannot be negated"),
            true => match input {
                Mode::Constant => CircuitCount::exact(2 * I::BITS, 0, 0, 0),
                _ => CircuitCount::exact(I::BITS, 0, I::BITS + 2, I::BITS + 4),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Neg<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn output_mode(input: &Self::Case) -> Mode {
        match input {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_neg<I: IntegerType + std::panic::UnwindSafe + Neg<Output = I> >(
        name: &str,
        value: I,
        mode: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode, value);
        let _case = format!("(-{})", a.eject_value());
        match value.checked_neg() {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.neg();
                assert_eq!(expected, candidate.eject_value());
                assert_count!(Integer<Circuit, I>, Neg<Output=Integer<Circuit, I>>, &mode);
                assert_output_mode!(candidate, Integer<Circuit, I>, Neg<Output=Integer<Circuit, I>>, &mode);
            }),
            None => {
                match mode {
                    Mode::Constant => check_unary_operation_halts(a, |a: Integer::<Circuit, I> | a.neg()),
                    _ => Circuit::scope(name, || {
                        let candidate = a.neg();
                        assert_count_fails!(Integer<Circuit, I>, Neg<Output=Integer<Circuit, I>>, &mode);
                        assert_output_mode!(candidate, Integer<Circuit, I>, Neg<Output=Integer<Circuit, I>>, &mode);
                    }),
                }
            }
        }
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::UnwindSafe + Neg<Output = I> >(
        mode: Mode,
    ) {
        // Check the 0 case.
        check_neg(&format!("Neg: {} zero", mode), I::zero(), mode);
        // Check the 1 case.
        check_neg(&format!("Neg: {} one", mode), -I::one(), mode);
        // Check random values.
        for i in 0..ITERATIONS {
            let value: I = UniformRand::rand(&mut test_rng());
            check_neg(&format!("Neg: {} {}", mode, i), value, mode);
        }
    }

    fn assert_unsigned_neg_halts<I: IntegerType + std::panic::UnwindSafe>(mode: Mode) {
        let candidate = Integer::<Circuit, I>::new(mode, UniformRand::rand(&mut test_rng()));
        let operation = std::panic::catch_unwind(|| candidate.neg());
        assert!(operation.is_err());
    }

    #[test]
    fn test_u8_neg() {
        type I = u8;
        assert_unsigned_neg_halts::<I>(Mode::Constant);
        assert_unsigned_neg_halts::<I>(Mode::Public);
        assert_unsigned_neg_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i8_neg() {
        type I = i8;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u16_neg() {
        type I = u16;
        assert_unsigned_neg_halts::<I>(Mode::Constant);
        assert_unsigned_neg_halts::<I>(Mode::Public);
        assert_unsigned_neg_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i16_neg() {
        type I = i16;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u32_neg() {
        type I = u32;
        assert_unsigned_neg_halts::<I>(Mode::Constant);
        assert_unsigned_neg_halts::<I>(Mode::Public);
        assert_unsigned_neg_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i32_neg() {
        type I = i32;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u64_neg() {
        type I = u64;
        assert_unsigned_neg_halts::<I>(Mode::Constant);
        assert_unsigned_neg_halts::<I>(Mode::Public);
        assert_unsigned_neg_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i64_neg() {
        type I = i64;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    fn test_u128_neg() {
        type I = u128;
        assert_unsigned_neg_halts::<I>(Mode::Constant);
        assert_unsigned_neg_halts::<I>(Mode::Public);
        assert_unsigned_neg_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i128_neg() {
        type I = i128;
        run_test::<I>(Mode::Constant);
        run_test::<I>(Mode::Public);
        run_test::<I>(Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_neg() {
        type I = i8;
        for value in I::MIN..=I::MAX {
            let name = format!("Neg: {}", Mode::Constant);
            check_neg(&name, value, Mode::Constant);

            let name = format!("Neg: {}", Mode::Public);
            check_neg(&name, value, Mode::Public);

            let name = format!("Neg: {}", Mode::Private);
            check_neg(&name, value, Mode::Private);
        }
    }
}
