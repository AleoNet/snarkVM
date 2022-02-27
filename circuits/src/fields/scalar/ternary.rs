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

use itertools::Itertools;

impl<E: Environment> Ternary for ScalarField<E> {
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let mut output = Vec::with_capacity(first.0.len());

        for (a, b) in first.0.iter().zip_eq(second.0.iter()) {
            output.push(Ternary::ternary(condition, a, b));
        }

        Self(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    #[test]
    fn test_ternary() {
        // Constant ? Constant : Constant
        {
            let a = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Constant, true);
            Circuit::scoped("Constant(true) ? Constant : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Constant, false);
            Circuit::scoped("Constant(false) ? Constant : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }

        // Constant ? Public : Private
        {
            let a = ScalarField::<Circuit>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Private, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Constant, true);
            Circuit::scoped("Constant(true) ? Public : Private", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Constant, false);
            Circuit::scoped("Constant(false) ? Public : Private", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }

        // Public ? Constant : Constant
        {
            let a = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Public, true);
            Circuit::scoped("Public(true) ? Constant : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Public, false);
            Circuit::scoped("Public(false) ? Constant : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }

        // Private ? Constant : Constant
        {
            let a = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scoped("Private(true) ? Constant : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scoped("Private(false) ? Constant : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }

        // Private ? Public : Constant
        {
            let a = ScalarField::<Circuit>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scoped("Private(true) ? Public : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(251, Circuit::num_private_in_scope());
                assert_eq!(251, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scoped("Private(false) ? Public : Constant", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(251, Circuit::num_private_in_scope());
                assert_eq!(251, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }

        // Private ? Constant : Public
        {
            let a = ScalarField::<Circuit>::new(Mode::Constant, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scoped("Private(true) ? Constant : Public", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(251, Circuit::num_private_in_scope());
                assert_eq!(251, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scoped("Private(false) ? Constant : Public", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(251, Circuit::num_private_in_scope());
                assert_eq!(251, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }

        // Private ? Private : Public
        {
            let a = ScalarField::<Circuit>::new(Mode::Private, UniformRand::rand(&mut thread_rng()));
            let b = ScalarField::<Circuit>::new(Mode::Public, UniformRand::rand(&mut thread_rng()));

            let condition = Boolean::new(Mode::Private, true);
            Circuit::scoped("Private(true) ? Private : Public", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(251, Circuit::num_private_in_scope());
                assert_eq!(251, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());

                assert!(output.is_eq(&a).eject_value());
                assert!(!output.is_eq(&b).eject_value());
            });

            let condition = Boolean::new(Mode::Private, false);
            Circuit::scoped("Private(false) ? Private : Public", || {
                let output = ScalarField::ternary(&condition, &a, &b);
                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(251, Circuit::num_private_in_scope());
                assert_eq!(251, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());

                assert!(!output.is_eq(&a).eject_value());
                assert!(output.is_eq(&b).eject_value());
            });
        }
    }
}
