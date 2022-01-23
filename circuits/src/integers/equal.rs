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

use itertools::Itertools;

impl<E: Environment, I: IntegerType> Equal<Self> for Integer<E, I> {
    type Boolean = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// TODO (@pranav) Number of constraints; Is extra logical and for Boolean::new(Mode::Constant, true) free?
    ///
    fn is_eq(&self, other: &Self) -> Self::Boolean {
        self.bits_le
            .iter()
            .zip_eq(other.bits_le.iter())
            .map(|(this, that)| this.is_eq(that))
            .fold(Boolean::new(Mode::Constant, true), |a, b| Boolean::and(&a, &b))
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    fn is_neq(&self, other: &Self) -> Self::Boolean {
        !self.is_eq(other)
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

    // #[rustfmt::skip]
    // fn check_is_eq<I: IntegerType, IC: IntegerTrait<I>>(
    //     name: &str,
    //     expected: bool,
    //     a: &IC,
    //     b: &IC,
    //     num_constants: usize,
    //     num_public: usize,
    //     num_private: usize,
    //     num_constraints: usize,
    // ) {
    //     Circuit::scoped(name, |scope| {
    //         let case = format!("({} == {})", a.eject_value(), b.eject_value());
    //
    //         let candidate = a.is_eq(b);
    //         assert_eq!(
    //             expected,
    //             candidate.eject_value(),
    //             "{} != {} := {}",
    //             expected,
    //             candidate.eject_value(),
    //             case
    //         );
    //
    //         assert_eq!(num_constants, scope.num_constants_in_scope(), "{} (num_constants)", case);
    //         assert_eq!(num_public, scope.num_public_in_scope(), "{} (num_public)", case);
    //         assert_eq!(num_private, scope.num_private_in_scope(), "{} (num_private)", case);
    //         assert_eq!(num_constraints, scope.num_constraints_in_scope(), "{} (num_constraints)", case);
    //         assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
    //     });
    // }

    // fn run_test<I: IntegerType>(
    //     mode_a: Mode,
    //     mode_b: Mode,
    //     num_constants: usize,
    //     num_public: usize,
    //     num_private: usize,
    //     num_constraints: usize,
    // ) where
    //     Standard: Distribution<I>,
    // {
    //     for i in 0..ITERATIONS {
    //         let first: I = UniformRand::rand(&mut thread_rng());
    //         let second: I = UniformRand::rand(&mut thread_rng());
    //         let expected = first == second;
    //
    //         let a = Integer::<Circuit, I>::new(mode_a, first);
    //         let b = Integer::new(mode_b, second);
    //
    //         let name = format!("Eq: a == b {}", i);
    //         check_is_eq(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
    //     }
    // }

    // #[test]
    // fn test_i8_is_eq_constant_constant() {
    //     type I = i8;
    //     run_test::<I>(Mode::Constant, Mode::Constant, 17, 0, 0, 0);
    // }
    //
    // #[test]
    // fn test_i8_is_eq_constant_public() {
    //     type I = i8;
    //     run_test::<I>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_i8_is_eq_constant_private() {
    //     type I = i8;
    //     run_test::<I>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_i8_is_eq_public_constant() {
    //     type I = i8;
    //     run_test::<I>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i8_is_eq_public_public() {
    //     type I = i8;
    //     run_test::<I>(Mode::Public, Mode::Public, Some((1, 16, 15, 46)));
    // }
    //
    // #[test]
    // fn test_i8_is_eq_public_private() {
    //     type I = i8;
    //     run_test::<I>(Mode::Public, Mode::Private, Some((1, 8, 23, 46)));
    // }
    //
    // #[test]
    // fn test_i8_is_eq_private_constant() {
    //     type I = i8;
    //     run_test::<I>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i8_is_eq_private_public() {
    //     type I = i8;
    //     run_test::<I>(Mode::Private, Mode::Public, Some((1, 8, 23, 46)));
    // }
    //
    // #[test]
    // fn test_i8_is_eq_private_private() {
    //     type I = i8;
    //     run_test::<I>(Mode::Private, Mode::Private, Some((1, 0, 31, 46)));
    // }

    // // Tests for i16
    //
    // #[test]
    // fn test_i16_is_eq_constant_constant() {
    //     run_test::<I>(Mode::Constant, Mode::Constant, Some((33, 0, 0, 0)));
    // }
    //
    // #[test]
    // fn test_i16_is_eq_constant_public() {
    //     run_test::<I>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_i16_is_eq_constant_private() {
    //     run_test::<I>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_i16_is_eq_public_constant() {
    //     run_test::<I>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i16_is_eq_public_public() {
    //     run_test::<I>(Mode::Public, Mode::Public, Some((1, 32, 31, 94)));
    // }
    //
    // #[test]
    // fn test_i16_is_eq_public_private() {
    //     run_test::<I>(Mode::Public, Mode::Private, Some((1, 16, 47, 94)));
    // }
    //
    // #[test]
    // fn test_i16_is_eq_private_constant() {
    //     run_test::<I>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i16_is_eq_private_public() {
    //     run_test::<I>(Mode::Private, Mode::Public, Some((1, 16, 47, 94)));
    // }
    //
    // #[test]
    // fn test_i16_is_eq_private_private() {
    //     run_test::<I>(Mode::Private, Mode::Private, Some((1, 0, 63, 94)));
    // }
    //
    // // Tests for i32
    //
    // #[test]
    // fn test_i32_is_eq_constant_constant() {
    //     run_test::<I>(Mode::Constant, Mode::Constant, Some((65, 0, 0, 0)));
    // }
    //
    // #[test]
    // fn test_i32_is_eq_constant_public() {
    //     run_test::<I>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_i32_is_eq_constant_private() {
    //     run_test::<I>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_i32_is_eq_public_constant() {
    //     run_test::<I>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i32_is_eq_public_public() {
    //     run_test::<I>(Mode::Public, Mode::Public, Some((1, 64, 63, 190)));
    // }
    //
    // #[test]
    // fn test_i32_is_eq_public_private() {
    //     run_test::<I>(Mode::Public, Mode::Private, Some((1, 32, 95, 190)));
    // }
    //
    // #[test]
    // fn test_i32_is_eq_private_constant() {
    //     run_test::<I>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i32_is_eq_private_public() {
    //     run_test::<I>(Mode::Private, Mode::Public, Some((1, 32, 95, 190)));
    // }
    //
    // #[test]
    // fn test_i32_is_eq_private_private() {
    //     run_test::<I>(Mode::Private, Mode::Private, Some((1, 0, 127, 190)));
    // }
    //
    // // Tests for i64
    //
    // #[test]
    // fn test_i64_is_eq_constant_constant() {
    //     run_test::<I>(Mode::Constant, Mode::Constant, Some((129, 0, 0, 0)));
    // }
    //
    // #[test]
    // fn test_i64_is_eq_constant_public() {
    //     run_test::<I>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_i64_is_eq_constant_private() {
    //     run_test::<I>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_i64_is_eq_public_constant() {
    //     run_test::<I>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i64_is_eq_public_public() {
    //     run_test::<I>(Mode::Public, Mode::Public, Some((1, 128, 127, 382)));
    // }
    //
    // #[test]
    // fn test_i64_is_eq_public_private() {
    //     run_test::<I>(Mode::Public, Mode::Private, Some((1, 64, 191, 382)));
    // }
    //
    // #[test]
    // fn test_i64_is_eq_private_constant() {
    //     run_test::<I>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i64_is_eq_private_public() {
    //     run_test::<I>(Mode::Private, Mode::Public, Some((1, 64, 191, 382)));
    // }
    //
    // #[test]
    // fn test_i64_is_eq_private_private() {
    //     run_test::<I>(Mode::Private, Mode::Private, Some((1, 0, 255, 382)));
    // }
    //
    // // Tests for i128
    //
    // #[test]
    // fn test_i128_is_eq_constant_constant() {
    //     run_test::<I>(Mode::Constant, Mode::Constant, Some((257, 0, 0, 0)));
    // }
    //
    // #[test]
    // fn test_i128_is_eq_constant_public() {
    //     run_test::<I>(Mode::Constant, Mode::Public, None);
    // }
    //
    // #[test]
    // fn test_i128_is_eq_constant_private() {
    //     run_test::<I>(Mode::Constant, Mode::Private, None);
    // }
    //
    // #[test]
    // fn test_i128_is_eq_public_constant() {
    //     run_test::<I>(Mode::Public, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i128_is_eq_public_public() {
    //     run_test::<I>(Mode::Public, Mode::Public, Some((1, 256, 255, 766)));
    // }
    //
    // #[test]
    // fn test_i128_is_eq_public_private() {
    //     run_test::<I>(Mode::Public, Mode::Private, Some((1, 128, 383, 766)));
    // }
    //
    // #[test]
    // fn test_i128_is_eq_private_constant() {
    //     run_test::<I>(Mode::Private, Mode::Constant, None);
    // }
    //
    // #[test]
    // fn test_i128_is_eq_private_public() {
    //     run_test::<I>(Mode::Private, Mode::Public, Some((1, 128, 383, 766)));
    // }
    //
    // #[test]
    // fn test_i128_is_eq_private_private() {
    //     run_test::<I>(Mode::Private, Mode::Private, Some((1, 0, 511, 766)));
    // }
}
