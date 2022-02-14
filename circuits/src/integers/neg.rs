// Copyright (C) 2019-2021 Aleo Systems Inc.
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
        match I::is_signed() {
            // Negate each bit in the representation of the `other` integer, and add `1` to the negated value.
            // Note: This addition must be checked as `-I::MIN` is an invalid operation.
            true => Integer::one().add_checked(&!self),
            false => E::halt("Attempted to negate an unsigned integer"),
        }
    }
}

impl<E: Environment, I: IntegerType> Neg for &Integer<E, I> {
    type Output = Integer<E, I>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_unsigned_halts<I: IntegerType + std::panic::UnwindSafe>(mode: Mode) {
        let value: I = UniformRand::rand(&mut thread_rng());
        check_unary_operation_halts(Integer::<Circuit, I>::new(mode, value), |a: Integer<Circuit, I> | { a.neg() })
    }

    #[rustfmt::skip]
    fn check_neg<I: IntegerType + std::panic::RefUnwindSafe + Neg<Output = I> >(
        name: &str,
        first: I,
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode, first);
        let case = format!("(-{})", a.eject_value());
        match first.checked_neg() {
            Some(value) => check_unary_operation_passes(name, &case, value, &a, |a: &Integer<Circuit, I> | { a.neg() }, num_constants, num_public, num_private, num_constraints),
            None => {
                match (mode) {
                    (Mode::Constant) => check_unary_operation_halts(&a, |a: &Integer<Circuit, I> | { a.neg() }),
                    _ => check_unary_operation_fails(name, &case, &a, |a: &Integer<Circuit, I> | { a.neg() }, num_constants, num_public, num_private, num_constraints),
                }
            }
        }
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::RefUnwindSafe + Neg<Output = I> >(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_neg = | name: &str, first: I | check_neg(name, first, mode, num_constants, num_public, num_private, num_constraints);

        // Check the 0 case.
        check_neg(&format!("Neg: {} zero", mode), I::zero());
        // Check the 1 case.
        check_neg(&format!("Neg: {} one", mode), -I::one());
        // Check random values.
        for i in 0..ITERATIONS {
            let value: I = UniformRand::rand(&mut thread_rng());
            check_neg(&format!("Neg: {} {}", mode, i), value);
        }
    }

    #[test]
    fn test_u8_neg() {
        type I = u8;
        check_unsigned_halts::<I>(Mode::Constant);
        check_unsigned_halts::<I>(Mode::Public);
        check_unsigned_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i8_neg() {
        type I = i8;
        run_test::<I>(Mode::Constant, 16, 0, 0, 0);
        run_test::<I>(Mode::Public, 10, 0, 12, 14);
        run_test::<I>(Mode::Private, 10, 0, 12, 14);
    }

    #[test]
    fn test_u16_neg() {
        type I = u16;
        check_unsigned_halts::<I>(Mode::Constant);
        check_unsigned_halts::<I>(Mode::Public);
        check_unsigned_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i16_neg() {
        type I = i16;
        run_test::<I>(Mode::Constant, 32, 0, 0, 0);
        run_test::<I>(Mode::Public, 18, 0, 20, 22);
        run_test::<I>(Mode::Private, 18, 0, 20, 22);
    }

    #[test]
    fn test_u32_neg() {
        type I = u32;
        check_unsigned_halts::<I>(Mode::Constant);
        check_unsigned_halts::<I>(Mode::Public);
        check_unsigned_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i32_neg() {
        type I = i32;
        run_test::<I>(Mode::Constant, 64, 0, 0, 0);
        run_test::<I>(Mode::Public, 34, 0, 36, 38);
        run_test::<I>(Mode::Private, 34, 0, 36, 38);
    }

    #[test]
    fn test_u64_neg() {
        type I = u64;
        check_unsigned_halts::<I>(Mode::Constant);
        check_unsigned_halts::<I>(Mode::Public);
        check_unsigned_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i64_neg() {
        type I = i64;
        run_test::<I>(Mode::Constant, 128, 0, 0, 0);
        run_test::<I>(Mode::Public, 66, 0, 68, 70);
        run_test::<I>(Mode::Private, 66, 0, 68, 70);
    }

    #[test]
    fn test_u128_neg() {
        type I = u128;
        check_unsigned_halts::<I>(Mode::Constant);
        check_unsigned_halts::<I>(Mode::Public);
        check_unsigned_halts::<I>(Mode::Private);
    }

    #[test]
    fn test_i128_neg() {
        type I = i128;
        run_test::<I>(Mode::Constant, 256, 0, 0, 0);
        run_test::<I>(Mode::Public, 130, 0, 132, 134);
        run_test::<I>(Mode::Private, 130, 0, 132, 134);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_neg() {
        type I = i8;
        for value in I::MIN..I::MAX {
            let name = format!("Neg: {}", Mode::Constant);
            check_neg(&name, value, Mode::Constant, 16, 0, 0, 0);

            let name = format!("Neg: {}", Mode::Public);
            check_neg(&name, value, Mode::Public, 10, 0, 12, 14);

            let name = format!("Neg: {}", Mode::Private);
            check_neg(&name, value, Mode::Private, 10, 0, 12, 14);
        }
    }
}
