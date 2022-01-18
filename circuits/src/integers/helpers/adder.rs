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

use crate::{And, Boolean, Environment, Or, Xor};

///
/// A single-bit binary adder with a carry bit.
///
/// https://en.wikipedia.org/wiki/Adder_(electronics)#Full_adder
///
/// sum = (a XOR b) XOR carry
/// carry = a AND b OR carry AND (a XOR b)
/// return (sum, carry)
///
pub trait Adder {
    type Carry;
    type Sum;

    /// Returns the sum of `self` and `other` as a sum bit and carry bit.
    fn adder(&self, other: &Self, carry: &Self) -> (Self::Sum, Self::Carry);
}

impl<E: Environment> Adder for Boolean<E> {
    type Carry = Boolean<E>;
    type Sum = Boolean<E>;

    /// Returns the sum of `self` and `other` as a sum bit and carry bit.
    fn adder(&self, other: &Self, carry: &Self) -> (Self::Sum, Self::Carry) {
        // Compute the sum bit.
        let c0 = self.xor(other); // <- Only pay for non-constants.
        let sum = c0.xor(carry); // <- Always pay after first non-constant `carry`.

        // Compute the carry bit.
        let c1 = self.and(other); // <- Only pay for non-constants.
        let c2 = carry.and(&c0); // <- Always pay after first non-constant `carry`.
        let carry = c1.or(&c2); // <- Always pay after first non-constant `carry`.

        (sum, carry)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Circuit, Mode};

    #[rustfmt::skip]
    fn check_adder(
        name: &str,
        expected_sum: bool,
        expected_carry: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
        c: Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let case = format!("({} ADD {} WITH {})", a.eject_value(), b.eject_value(), c.eject_value());

            let (candidate_sum, candidate_carry) = a.adder(&b, &c);
            assert_eq!(
                expected_sum,
                candidate_sum.eject_value(),
                "SUM {} != {} := {}",
                expected_sum,
                candidate_sum.eject_value(),
                case
            );
            assert_eq!(
                expected_carry,
                candidate_carry.eject_value(),
                "CARRY {} != {} := {}",
                expected_carry,
                candidate_carry.eject_value(),
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
    fn check_false_add_false_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // false ADD false WITH false => (false, false)
        let expected_sum = false;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_adder("false ADD false WITH false", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_false_add_false_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // false ADD false WITH true => (true, false)
        let expected_sum = true;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_adder("false ADD false WITH true", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_false_add_true_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // false ADD true WITH false => (true, false)
        let expected_sum = true;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_adder("false ADD true WITH false", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_false_add_true_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // false ADD true WITH true => (false, true)
        let expected_sum = false;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_adder("false ADD true WITH true", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_add_false_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // true ADD false WITH false => (true, false)
        let expected_sum = true;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_adder("true ADD false WITH false", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_add_false_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // true ADD false WITH true => (false, true)
        let expected_sum = false;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_adder("true ADD false WITH true", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_add_true_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // true ADD true WITH false => (false, true)
        let expected_sum = false;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_adder("true ADD true WITH false", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_add_true_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        // true ADD true WITH true => (true, true)
        let expected_sum = true;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_adder("true ADD true WITH true", expected_sum, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[test]
    fn test_constant_add_constant_with_constant() {
        check_false_add_false_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_add_false_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_true_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_true_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_add_constant_with_public() {
        check_false_add_false_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_false_add_false_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_false_add_true_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_false_add_true_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_add_false_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_add_false_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_add_true_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_add_true_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_add_constant_with_private() {
        check_false_add_false_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_false_add_false_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_false_add_true_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_false_add_true_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_add_false_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_add_false_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_add_true_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_add_true_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_add_public_with_constant() {
        check_false_add_false_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_false_add_false_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 1, 2); // <- Differs
        check_true_add_true_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_true_add_true_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 1, 2); // <- Differs
    }

    #[test]
    fn test_constant_add_public_with_public() {
        check_false_add_false_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 4);
        check_false_add_true_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 4);
        check_false_add_true_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 4);
        check_true_add_false_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_constant_add_public_with_private() {
        check_false_add_false_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 4);
        check_false_add_true_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 4);
        check_false_add_true_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 4);
        check_true_add_false_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_constant_add_private_with_constant() {
        check_false_add_false_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_false_add_false_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 1, 2); // <- Differs
        check_true_add_true_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_true_add_true_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 1, 2); // <- Differs
    }

    #[test]
    fn test_constant_add_private_with_public() {
        check_false_add_false_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 4);
        check_false_add_true_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 4);
        check_false_add_true_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 4);
        check_true_add_false_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_constant_add_private_with_private() {
        check_false_add_false_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 4);
        check_false_add_true_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 4);
        check_false_add_true_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 4);
        check_true_add_false_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_public_add_constant_with_constant() {
        check_false_add_false_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_add_false_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_add_true_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 1, 2); // <- Differs
        check_true_add_false_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_false_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_true_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_add_true_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 1, 2); // <- Differs
    }

    #[test]
    fn test_public_add_constant_with_public() {
        check_false_add_false_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 4);
        check_false_add_true_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_false_add_true_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 4);
        check_true_add_false_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 4);
        check_true_add_true_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_public_add_constant_with_private() {
        check_false_add_false_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 4);
        check_false_add_true_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_false_add_true_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 4);
        check_true_add_false_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 4);
        check_true_add_true_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_public_add_public_with_constant() {
        check_false_add_false_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 6); // <- Differs
        check_false_add_true_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 4);
        check_false_add_true_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 4);
        check_true_add_false_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 4);
        check_true_add_true_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_public_add_public_with_public() {
        check_false_add_false_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_false_add_false_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_false_add_true_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_false_add_true_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_true_add_false_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_true_add_false_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_true_add_true_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
        check_true_add_true_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 10);
    }

    #[test]
    fn test_public_add_public_with_private() {
        check_false_add_false_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_false_add_false_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_false_add_true_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_false_add_true_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_true_add_false_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_true_add_false_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_true_add_true_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
        check_true_add_true_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 10);
    }

    #[test]
    fn test_public_add_private_with_constant() {
        check_false_add_false_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 4);
        check_false_add_false_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 6); // <- Differs
        check_false_add_true_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 4);
        check_false_add_true_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 6); // <- Differs
        check_true_add_false_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 4);
        check_true_add_false_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 6); // <- Differs
        check_true_add_true_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 4);
        check_true_add_true_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 6); // <- Differs
    }

    #[test]
    fn test_public_add_private_with_public() {
        check_false_add_false_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_false_add_false_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_false_add_true_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_false_add_true_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_true_add_false_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_true_add_false_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_true_add_true_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
        check_true_add_true_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 10);
    }

    #[test]
    fn test_public_add_private_with_private() {
        check_false_add_false_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_false_add_false_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_false_add_true_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_false_add_true_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_true_add_false_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_true_add_false_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_true_add_true_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
        check_true_add_true_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 10);
    }
}
