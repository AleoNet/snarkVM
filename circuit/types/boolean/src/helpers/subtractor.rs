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

impl<E: Environment> Subtractor for Boolean<E> {
    type Borrow = Boolean<E>;
    type Difference = Boolean<E>;

    /// Returns the difference of `self` and `other` as a difference bit and borrow bit.
    fn subtractor(&self, other: &Self, borrow: &Self) -> (Self::Difference, Self::Borrow) {
        // Compute the difference bit.
        let c0 = self ^ other;
        let difference = &c0 ^ borrow;

        // Compute the borrow bit.
        let c1 = !self & other;
        let c2 = borrow & !c0;
        let borrow = c1 | c2;

        (difference, borrow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_subtractor(
        name: &str,
        expected_difference: bool,
        expected_borrow: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
        c: Boolean<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        Circuit::scope(name, || {
            let case = format!("({} SUB {} WITH {})", a.eject_value(), b.eject_value(), c.eject_value());
            let (candidate_difference, candidate_borrow) = a.subtractor(&b, &c);
            assert_eq!(expected_difference, candidate_difference.eject_value(), "DIFF {}", case);
            assert_eq!(expected_borrow, candidate_borrow.eject_value(), "BORROW {}", case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
    }

    #[rustfmt::skip]
    fn check_false_sub_false_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // false SUB false WITH false => (false, false)
        let expected_difference = false;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_subtractor("false SUB false WITH false", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_false_sub_false_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // false SUB false WITH true => (true, true)
        let expected_difference = true;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_subtractor("false SUB false WITH true", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_false_sub_true_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // false SUB true WITH false => (true, true)
        let expected_difference = true;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_subtractor("false SUB true WITH false", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_false_sub_true_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // false SUB true WITH true => (false, true)
        let expected_difference = false;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, false);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_subtractor("false SUB true WITH true", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_sub_false_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // true SUB false WITH false => (true, false)
        let expected_difference = true;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_subtractor("true SUB false WITH false", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_sub_false_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // true SUB false WITH true => (false, false)
        let expected_difference = false;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, false);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_subtractor("true SUB false WITH true", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_sub_true_with_false(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // true SUB true WITH false => (false, false)
        let expected_difference = false;
        let expected_carry = false;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, false);
        check_subtractor("true SUB true WITH false", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn check_true_sub_true_with_true(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64
    ) {
        // true SUB true WITH true => (true, true)
        let expected_difference = true;
        let expected_carry = true;
        let a = Boolean::<Circuit>::new(mode_a, true);
        let b = Boolean::<Circuit>::new(mode_b, true);
        let c = Boolean::<Circuit>::new(mode_c, true);
        check_subtractor("true SUB true WITH true", expected_difference, expected_carry, a, b, c, num_constants, num_public, num_private, num_constraints);
    }

    #[test]
    fn test_constant_sub_constant_with_constant() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_false_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_true_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_true_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_false_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_false_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_false(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_true(Mode::Constant, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_sub_constant_with_public() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_false_sub_false_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_false_sub_true_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_false_sub_true_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_sub_false_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_sub_false_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_sub_true_with_false(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
        check_true_sub_true_with_true(Mode::Constant, Mode::Constant, Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_sub_constant_with_private() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_false_sub_false_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_false_sub_true_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_false_sub_true_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_sub_false_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_sub_false_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_sub_true_with_false(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
        check_true_sub_true_with_true(Mode::Constant, Mode::Constant, Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_sub_public_with_constant() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_false_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 1, 1); // <- Differs
        check_false_sub_true_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_true_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 1, 1); // <- Differs
        check_true_sub_false_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_false_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_false(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_true(Mode::Constant, Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_sub_public_with_public() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_false_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 2);
        check_true_sub_true_with_false(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 2);
        check_true_sub_true_with_true(Mode::Constant, Mode::Public, Mode::Public, 0, 0, 2, 2);
    }

    #[test]
    fn test_constant_sub_public_with_private() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_false_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 2);
        check_true_sub_true_with_false(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 2);
        check_true_sub_true_with_true(Mode::Constant, Mode::Public, Mode::Private, 0, 0, 2, 2);
    }

    #[test]
    fn test_constant_sub_private_with_constant() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_false_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 1, 1); // <- Differs
        check_false_sub_true_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_true_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 1, 1); // <- Differs
        check_true_sub_false_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_false_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_false(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_true(Mode::Constant, Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_sub_private_with_public() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_false_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 2);
        check_true_sub_true_with_false(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 2);
        check_true_sub_true_with_true(Mode::Constant, Mode::Private, Mode::Public, 0, 0, 2, 2);
    }

    #[test]
    fn test_constant_sub_private_with_private() {
        check_false_sub_false_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_false_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 2);
        check_true_sub_true_with_false(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 2);
        check_true_sub_true_with_true(Mode::Constant, Mode::Private, Mode::Private, 0, 0, 2, 2);
    }

    #[test]
    fn test_public_sub_constant_with_constant() {
        check_false_sub_false_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_false_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_true_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_false_sub_true_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 1, 1); // <- Differs
        check_true_sub_false_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_false_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_false(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 0, 0);
        check_true_sub_true_with_true(Mode::Public, Mode::Constant, Mode::Constant, 0, 0, 1, 1); // <- Differs
    }

    #[test]
    fn test_public_sub_constant_with_public() {
        check_false_sub_false_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 2);
        check_false_sub_false_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 2);
        check_false_sub_true_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 2, 2);
        check_true_sub_true_with_false(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 3); // <- Differs
        check_true_sub_true_with_true(Mode::Public, Mode::Constant, Mode::Public, 0, 0, 3, 3); // <- Differs
    }

    #[test]
    fn test_public_sub_constant_with_private() {
        check_false_sub_false_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 2);
        check_false_sub_false_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 2);
        check_false_sub_true_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 2, 2);
        check_true_sub_true_with_false(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 3); // <- Differs
        check_true_sub_true_with_true(Mode::Public, Mode::Constant, Mode::Private, 0, 0, 3, 3); // <- Differs
    }

    #[test]
    fn test_public_sub_public_with_constant() {
        check_false_sub_false_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 2);
        check_false_sub_false_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 2);
        check_false_sub_true_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 3); // <- Differs
        check_true_sub_true_with_false(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 2, 2);
        check_true_sub_true_with_true(Mode::Public, Mode::Public, Mode::Constant, 0, 0, 3, 3); // <- Differs
    }

    #[test]
    fn test_public_sub_public_with_public() {
        check_false_sub_false_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_false_sub_false_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_false_sub_true_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_false_sub_true_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_true_sub_false_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_true_sub_false_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_true_sub_true_with_false(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
        check_true_sub_true_with_true(Mode::Public, Mode::Public, Mode::Public, 0, 0, 5, 5);
    }

    #[test]
    fn test_public_sub_public_with_private() {
        check_false_sub_false_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_false_sub_false_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_false_sub_true_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_false_sub_true_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_true_sub_false_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_true_sub_false_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_true_sub_true_with_false(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
        check_true_sub_true_with_true(Mode::Public, Mode::Public, Mode::Private, 0, 0, 5, 5);
    }

    #[test]
    fn test_public_sub_private_with_constant() {
        check_false_sub_false_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 2);
        check_false_sub_false_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 3); // <- Differs
        check_false_sub_true_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 2);
        check_false_sub_true_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 3); // <- Differs
        check_true_sub_false_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 2);
        check_true_sub_false_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 3); // <- Differs
        check_true_sub_true_with_false(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 2, 2);
        check_true_sub_true_with_true(Mode::Public, Mode::Private, Mode::Constant, 0, 0, 3, 3); // <- Differs
    }

    #[test]
    fn test_public_sub_private_with_public() {
        check_false_sub_false_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_false_sub_false_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_false_sub_true_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_false_sub_true_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_true_sub_false_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_true_sub_false_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_true_sub_true_with_false(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
        check_true_sub_true_with_true(Mode::Public, Mode::Private, Mode::Public, 0, 0, 5, 5);
    }

    #[test]
    fn test_public_sub_private_with_private() {
        check_false_sub_false_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_false_sub_false_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_false_sub_true_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_false_sub_true_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_true_sub_false_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_true_sub_false_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_true_sub_true_with_false(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
        check_true_sub_true_with_true(Mode::Public, Mode::Private, Mode::Private, 0, 0, 5, 5);
    }
}
