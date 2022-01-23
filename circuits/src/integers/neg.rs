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

    fn neg(self) -> Self::Output {
        match I::is_signed() {
            true => {
                // Negate each bit in the representation of the `other` integer.
                let negated = Integer::from_bits(self.bits_le.iter().map(|b| !b).collect());
                // Add `1` to the negated value.
                negated.add_wrapped(&Integer::one())
            }
            false => E::halt("Attempted to negate an unsigned integer"),
        }
    }
}

impl<E: Environment, I: IntegerType> Neg for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

    #[rustfmt::skip]
    fn check_neg<I: IntegerType, IC: IntegerTrait<I>>(
        name: &str,
        expected: I,
        candidate: IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let case = format!("-{}", candidate.eject_value());

            let candidate = -candidate;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            assert_eq!(num_constants, scope.num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, scope.num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, scope.num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, scope.num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    #[rustfmt::skip]
    fn check_unsigned_halts<I: IntegerType + std::panic::UnwindSafe>(mode: Mode) where Standard: Distribution<I> {
        let value: I = UniformRand::rand(&mut thread_rng());
        let candidate = Integer::<Circuit, I>::new(mode, value);
        let result = std::panic::catch_unwind(|| candidate.neg());
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + Neg<Output = I>>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        Standard: Distribution<I>,
    {
        for i in 0..ITERATIONS {
            let name = format!("Neg: {}", i);
            let value: I = UniformRand::rand(&mut thread_rng());
            let expected = match value.checked_neg() {
                Some(negated) => negated,
                None => continue
            };
            let candidate = Integer::<Circuit, I>::new(mode, value);

            check_neg::<I, Integer<Circuit, I>>(&name, expected, candidate, num_constants, num_public, num_private, num_constraints);
        }

        // Check the 0 case.
        let candidate = Integer::<Circuit, I>::new(mode, I::zero());
        check_neg::<I, Integer<Circuit, I>>("Neg: zero", I::zero(), candidate, num_constants, num_public, num_private, num_constraints);

        // Check the 1 case.
        let candidate = Integer::<Circuit, I>::new(mode, I::one());
        check_neg::<I, Integer<Circuit, I>>("Neg: one", -I::one(), candidate, num_constants, num_public, num_private, num_constraints);
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
        run_test::<I>(Mode::Public, 25, 0, 13, 13);
        run_test::<I>(Mode::Private, 34, 0, 26, 26);
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
        run_test::<I>(Mode::Public, 49, 0, 29, 29);
        run_test::<I>(Mode::Private, 66, 0, 58, 58);
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
        run_test::<I>(Mode::Public, 97, 0, 61, 61);
        run_test::<I>(Mode::Private, 130, 0, 122, 122);
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
        run_test::<I>(Mode::Public, 193, 0, 125, 125);
        run_test::<I>(Mode::Private, 258, 0, 250, 250);
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
        run_test::<I>(Mode::Public, 385, 0, 253, 253);
        run_test::<I>(Mode::Private, 514, 0, 506, 506);
    }
}
