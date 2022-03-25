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
use snarkvm_utilities::{FromBytes, ToBytes};

impl<E: Environment> Compare<Scalar<E>> for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Self) -> Self::Boolean {
        let scalar_modulus = match E::ScalarField::modulus().to_bytes_le() {
            Ok(modulus_bytes) => match E::BaseField::from_bytes_le(&modulus_bytes) {
                Ok(modulus) => modulus,
                Err(error) => E::halt(format!("Failed to load the scalar modulus as a constant: {error}")),
            },
            Err(error) => E::halt(format!("Failed to retrieve the scalar modulus as bytes: {error}")),
        };
        if scalar_modulus.to_repr() <= E::BaseField::modulus_minus_one_div_two() {
            if self.is_constant() && other.is_constant() {
                Boolean::new(Mode::Constant, self.eject_value() < other.eject_value())
            } else {
                (self.to_field() - other.to_field()).double().to_bits_be().pop().unwrap()
            }
        } else {
            let mut is_less_than = Boolean::constant(false);
            let mut are_previous_bits_equal = Boolean::constant(true);

            // Initialize an iterator over `self` and `other` from MSB to LSB.
            let bits_be = self.bits_le.iter().rev().zip_eq(other.bits_le.iter().rev());

            for (index, (self_bit, other_bit)) in bits_be.enumerate() {
                // Determine if `self` is less than `other` up to the `index`-th bit.
                is_less_than |= &are_previous_bits_equal & (!self_bit & other_bit);

                // Skip the update to the LSB, as this boolean is subsequently discarded.
                if index != self.bits_le.len() - 1 {
                    are_previous_bits_equal &= self_bit.is_equal(other_bit);
                }
            }
            is_less_than
        }
    }

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Self) -> Self::Boolean {
        other.is_less_than(self)
    }

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Self) -> Self::Boolean {
        other.is_greater_than_or_equal(self)
    }

    /// Returns `true` if `self` is greater than or equal to `other`.
    fn is_greater_than_or_equal(&self, other: &Self) -> Self::Boolean {
        !self.is_less_than(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    // TODO: Consider exposing test utilities in integers to all circuit types.

    #[rustfmt::skip]
    fn check_compare(
        name: &str,
        first: <Circuit as Environment>::ScalarField,
        second: <Circuit as Environment>::ScalarField,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Check `is_less_than`.
        let expected = first < second;
        let case = format!("({} < {})", first, second);

        let a = Scalar::<Circuit>::new(mode_a, first);
        let b = Scalar::<Circuit>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.is_less_than(&b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();

        // Check `is_less_than_or_equal`
        let expected = first <= second;
        let case = format!("({} <= {})", first, second);

        let a = Scalar::<Circuit>::new(mode_a, first);
        let b = Scalar::<Circuit>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.is_less_than_or_equal(&b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();

        // Check `is_greater_than`
        let expected = first > second;
        let case = format!("({} > {})", first, second);

        let a = Scalar::<Circuit>::new(mode_a, first);
        let b = Scalar::<Circuit>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.is_greater_than(&b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();

        // Check `is_greater_than_or_equal`
        let expected = first >= second;
        let case = format!("({} >= {})", first, second);

        let a = Scalar::<Circuit>::new(mode_a, first);
        let b = Scalar::<Circuit>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.is_greater_than_or_equal(&b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    #[rustfmt::skip]
    fn run_test(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let second: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());

            let name = format!("Compare: {}, {}, {}", mode_a, mode_b, i);
            check_compare(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
        }
    }

    #[test]
    fn test_constant_compare_with_constant() {
        run_test(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_constant_compare_with_public() {
        run_test(Mode::Constant, Mode::Public, 0, 0, 253, 254);
    }

    #[test]
    fn test_constant_compare_with_private() {
        run_test(Mode::Constant, Mode::Private, 0, 0, 253, 254);
    }

    #[test]
    fn test_public_compare_with_constant() {
        run_test(Mode::Public, Mode::Constant, 0, 0, 253, 254);
    }

    #[test]
    fn test_private_compare_with_constant() {
        run_test(Mode::Private, Mode::Constant, 0, 0, 253, 254);
    }

    #[test]
    fn test_public_compare_with_public() {
        run_test(Mode::Public, Mode::Public, 0, 0, 253, 254);
    }

    #[test]
    fn test_public_compare_with_private() {
        run_test(Mode::Public, Mode::Private, 0, 0, 253, 254);
    }

    #[test]
    fn test_private_compare_with_public() {
        run_test(Mode::Private, Mode::Public, 0, 0, 253, 254);
    }

    #[test]
    fn test_private_compare_with_private() {
        run_test(Mode::Private, Mode::Private, 0, 0, 253, 254);
    }
}
