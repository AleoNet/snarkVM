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

impl<E: Environment, I: IntegerType> Not for Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        // Flip all bits.
        Integer { bits_le: self.bits_le.iter().map(|b| !b).collect(), phantom: Default::default() }
    }
}

impl<E: Environment, I: IntegerType> Not for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        !(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_not<I: IntegerType, IC: IntegerTrait<Circuit, I>>(
        name: &str,
        expected: I,
        candidate: IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let case = format!("!{}", candidate.eject_value());

            let candidate = !candidate;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + Not<Output = I>>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let name = format!("Not: {} {}", mode, i);
            let value: I = UniformRand::rand(&mut thread_rng());
            let expected = !value;
            let candidate = Integer::<Circuit, I>::new(mode, value);

            check_not::<I, Integer<Circuit, I>>(&name, expected, candidate, num_constants, num_public, num_private, num_constraints);
        }

        // Check the 0 case.
        let name = format!("Not: {} zero", mode);
        let candidate = Integer::<Circuit, I>::new(mode, I::zero());
        check_not::<I, Integer<Circuit, I>>(&name, !I::zero(), candidate, num_constants, num_public, num_private, num_constraints);

        // Check the 1 case.
        let name = format!("Not: {} one", mode);
        let candidate = Integer::<Circuit, I>::new(mode, I::one());
        check_not::<I, Integer<Circuit, I>>(&name, !I::one(), candidate, num_constants, num_public, num_private, num_constraints);
    }

    #[test]
    fn test_u8_not() {
        type I = u8;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_not() {
        type I = i8;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_not() {
        type I = u16;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_not() {
        type I = i16;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_not() {
        type I = u32;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_not() {
        type I = i32;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_not() {
        type I = u64;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_not() {
        type I = i64;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_not() {
        type I = u128;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_not() {
        type I = i128;
        run_test::<I>(Mode::Constant, 0, 0, 0, 0);
        run_test::<I>(Mode::Public, 0, 0, 0, 0);
        run_test::<I>(Mode::Private, 0, 0, 0, 0);
    }
}
