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

impl<E: Environment, I: IntegerType> AbsWrapped for Integer<E, I> {
    type Output = Integer<E, I>;

    fn abs_wrapped(self) -> Self::Output {
        (&self).abs_wrapped()
    }
}

impl<E: Environment, I: IntegerType> AbsWrapped for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn abs_wrapped(self) -> Self::Output {
        match I::is_signed() {
            true => Integer::ternary(self.msb(), &Integer::zero().sub_wrapped(self), self),
            false => self.clone(),
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
    fn check_abs<I: IntegerType + std::panic::UnwindSafe>(
        name: &str,
        value: I,
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode, value);
        let case = format!("(!{})", a.eject_value());
        let expected = value.wrapping_abs();
        check_unary_operation_passes(name, &case, expected, a, |a: Integer<Circuit, I> | a.abs_wrapped(), num_constants, num_public, num_private, num_constraints);
    }

    fn run_test<I: IntegerType + std::panic::UnwindSafe>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let name = format!("Abs: {} {}", mode, i);
            let value: I = UniformRand::rand(&mut test_rng());
            check_abs(&name, value, mode, num_constants, num_public, num_private, num_constraints);
        }

        // Check the 0 case.
        let name = format!("Abs: {} zero", mode);
        check_abs(&name, I::zero(), mode, num_constants, num_public, num_private, num_constraints);

        // Check the 1 case.
        let name = format!("Abs: {} one", mode);
        check_abs(&name, I::one(), mode, num_constants, num_public, num_private, num_constraints);

        // Check the I::MIN (wrapped) case.
        let name = format!("Abs: {} one", mode);
        check_abs(&name, I::MIN, mode, num_constants, num_public, num_private, num_constraints);
    }

    #[test]
    fn test_u8_abs() {
        type I = u8;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_abs() {
        type I = i8;
        run_test::<I>(Mode::Constant, 16, 0, 0, 0);
        run_test::<I>(Mode::Public, 8, 0, 17, 18);
        run_test::<I>(Mode::Private, 8, 0, 17, 18);
    }

    #[test]
    fn test_u16_abs() {
        type I = u16;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_abs() {
        type I = i16;
        run_test::<I>(Mode::Constant, 32, 0, 0, 0);
        run_test::<I>(Mode::Public, 16, 0, 33, 34);
        run_test::<I>(Mode::Private, 16, 0, 33, 34);
    }

    #[test]
    fn test_u32_abs() {
        type I = u32;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_abs() {
        type I = i32;
        run_test::<I>(Mode::Constant, 64, 0, 0, 0);
        run_test::<I>(Mode::Public, 32, 0, 65, 66);
        run_test::<I>(Mode::Private, 32, 0, 65, 66);
    }

    #[test]
    fn test_u64_abs() {
        type I = u64;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_abs() {
        type I = i64;
        run_test::<I>(Mode::Constant, 128, 0, 0, 0);
        run_test::<I>(Mode::Public, 64, 0, 129, 130);
        run_test::<I>(Mode::Private, 64, 0, 129, 130);
    }

    #[test]
    fn test_u128_abs() {
        type I = u128;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_abs() {
        type I = i128;
        run_test::<I>(Mode::Constant, 256, 0, 0, 0);
        run_test::<I>(Mode::Public, 128, 0, 257, 258);
        run_test::<I>(Mode::Private, 128, 0, 257, 258);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_abs() {
        type I = u8;
        for value in I::MIN..=I::MAX {
            let name = format!("Abs: {}", Mode::Constant);
            check_abs(&name, value, Mode::Constant, 0, 0, 0, 0);

            let name = format!("Abs: {}", Mode::Public);
            check_abs(&name, value, Mode::Public, 0, 0, 0, 0);

            let name = format!("Abs: {}", Mode::Private);
            check_abs(&name, value, Mode::Private, 0, 0, 0, 0);
        }
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_abs() {
        type I = i8;
        for value in I::MIN..=I::MAX {
            let name = format!("Abs: {}", Mode::Constant);
            check_abs(&name, value, Mode::Constant, 16, 0, 0, 0);

            let name = format!("Abs: {}", Mode::Public);
            check_abs(&name, value, Mode::Public, 8, 0, 17, 18);

            let name = format!("Abs: {}", Mode::Private);
            check_abs(&name, value, Mode::Private, 8, 0, 17, 18);
        }
    }
}
