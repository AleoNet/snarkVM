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

impl<E: Environment> Ternary for Scalar<E> {
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let mut bits_le = Vec::with_capacity(first.bits_le.len());

        for (a, b) in first.bits_le.iter().zip_eq(second.bits_le.iter()) {
            bits_le.push(Ternary::ternary(condition, a, b));
        }

        Self { bits_le }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    #[test]
    fn test_ternary() {
        // Constant ? Constant : Constant
        {
            let a = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::constant(true);
            Circuit::scope("Constant(true) ? Constant : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::constant(false);
            Circuit::scope("Constant(false) ? Constant : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }

        // Constant ? Public : Private
        {
            let a = Scalar::<Circuit>::new(Mode::Public, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Private, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::constant(true);
            Circuit::scope("Constant(true) ? Public : Private", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::constant(false);
            Circuit::scope("Constant(false) ? Public : Private", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }

        // Public ? Constant : Constant
        {
            let a = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::new(Mode::Public, true);
            Circuit::scope("Public(true) ? Constant : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Public, false);
            Circuit::scope("Public(false) ? Constant : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }

        // Private ? Constant : Constant
        {
            let a = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scope("Private(true) ? Constant : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scope("Private(false) ? Constant : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 0, 0);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }

        // Private ? Public : Constant
        {
            let a = Scalar::<Circuit>::new(Mode::Public, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scope("Private(true) ? Public : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 251, 251);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scope("Private(false) ? Public : Constant", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 251, 251);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }

        // Private ? Constant : Public
        {
            let a = Scalar::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Public, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scope("Private(true) ? Constant : Public", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 251, 251);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scope("Private(false) ? Constant : Public", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 251, 251);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }

        // Private ? Private : Public
        {
            let a = Scalar::<Circuit>::new(Mode::Private, UniformRand::rand(&mut test_rng()));
            let b = Scalar::<Circuit>::new(Mode::Public, UniformRand::rand(&mut test_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scope("Private(true) ? Private : Public", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 251, 251);

                assert!(output.is_equal(&a).eject_value());
                assert!(!output.is_equal(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scope("Private(false) ? Private : Public", || {
                let output = Scalar::ternary(&condition, &a, &b);
                assert_scope!(0, 0, 251, 251);

                assert!(!output.is_equal(&a).eject_value());
                assert!(output.is_equal(&b).eject_value());
            });
        }
    }
}
