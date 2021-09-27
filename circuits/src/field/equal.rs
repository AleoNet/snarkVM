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

impl<E: Environment> Equal<Self> for Field<E> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// This method costs 3 constraints.
    ///
    fn is_eq(&self, other: &Self) -> Self::Output {
        !self.is_neq(other)
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    /// This method costs 3 constraints.
    ///
    fn is_neq(&self, other: &Self) -> Self::Output {
        match (self.0.is_constant(), other.0.is_constant()) {
            (true, true) => Boolean::new(Mode::Constant, self.to_value() != other.to_value()),
            _ => {
                let this = self.to_value();
                let that = other.to_value();

                // Compute a boolean that is `true` if `this` and `that` are not equivalent.
                let is_neq = Boolean::new(Mode::Private, this != that);

                // Assign the expected multiplier.
                let multiplier = E::new_variable(Mode::Private, match this != that {
                    true => (this - that).inverse().expect("Failed to compute a native inverse"),
                    false => E::BaseField::one(),
                });

                //
                // Inequality Enforcement
                // ----------------------------------------------------------------
                // Check 1:  (a - b) * multiplier = is_neq
                // Check 2:  (a - b) * not(is_neq) = 0
                //
                //
                // Case 1: a == b AND is_neq == 0 (honest)
                // ----------------------------------------------------------------
                // Check 1:  (a - b) * 1 = 0
                //                 a - b = 0
                // => As a == b, is_neq is correct.
                //
                // Check 2:  (a - b) * not(0) = 0
                //                      a - b = 0
                // => As a == b, is_neq is correct.
                //
                // Remark: While the multiplier = 1 here, letting multiplier := n,
                //         for n as any field element, also holds.
                //
                //
                // Case 2: a == b AND is_neq == 1 (dishonest)
                // ----------------------------------------------------------------
                // Check 1:  (a - b) * 1 = 1
                //                 a - b = 1
                // => As a == b, the is_neq is incorrect.
                //
                // Remark: While the multiplier = 1 here, letting multiplier := n,
                //         for n as any field element, also holds.
                //
                //
                // Case 3a: a != b AND is_neq == 0 AND multiplier = 0 (dishonest)
                // ----------------------------------------------------------------
                // Check 2:  (a - b) * not(0) = 0
                //                      a - b = 0
                // => As a != b, is_neq is incorrect.
                //
                // Case 3b: a != b AND is_neq == 0 AND multiplier = 1 (dishonest)
                // ----------------------------------------------------------------
                // Check 1:  (a - b) * 1 = 0
                //                 a - b = 0
                // => As a != b, is_neq is incorrect.
                //
                // Remark: While the multiplier = 1 here, letting multiplier = n,
                //         for n as any field element (n != 0), also holds.
                //
                //
                // Case 4a: a != b AND is_neq == 1 AND multiplier = n [!= (a - b)^(-1)] (dishonest)
                // ---------------------------------------------------------------------------------
                // Check 1:  (a - b) * n = 1
                // => As n != (a - b)^(-1), is_neq is incorrect.
                //
                // Case 4b: a != b AND is_neq == 1 AND multiplier = (a - b)^(-1) (honest)
                // ---------------------------------------------------------------------------------
                // Check 1:  (a - b) * (a - b)^(-1) = 1
                //                                1 = 1
                // => is_neq is trivially correct.
                //
                // Check 2:  (a - b) * not(1) = 0
                //                          0 = 0
                // => is_neq is trivially correct.
                //

                // Compute `self` - `other`.
                let delta = &self.0 - &other.0;

                // Negate `is_neq`.
                let is_eq = !is_neq.clone();

                // Check 1: (a - b) * multiplier = is_neq
                E::enforce(|| (delta.clone(), multiplier, is_neq.clone()));

                // Check 2: (a - b) * not(is_neq) = 0
                E::enforce(|| (delta, is_eq, E::zero()));

                is_neq
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 1_000;

    #[test]
    fn test_is_eq() {
        let zero = <Circuit as Environment>::BaseField::zero();
        let one = <Circuit as Environment>::BaseField::one();

        // Basic `true` and `false` cases
        {
            let mut accumulator = one + one;

            for _ in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_eq(&b);
                assert_eq!(true, is_eq.to_value());

                let a = Field::<Circuit>::new(Mode::Private, one);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_eq(&b);
                assert_eq!(false, is_eq.to_value());

                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator - one);
                let is_eq = a.is_eq(&b);
                assert_eq!(false, is_eq.to_value());

                accumulator = accumulator + &one;
            }
        }

        // Constant variables
        Circuit::scoped("Constant", |scope| {
            let mut accumulator = zero;

            for i in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Constant, accumulator);
                let b = Field::<Circuit>::new(Mode::Constant, accumulator);

                let is_eq = a.is_eq(&b);
                assert_eq!(true, is_eq.to_value());

                assert_eq!((i + 1) * 3, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());

                accumulator = accumulator + &one;
            }
        });

        // Public variables
        Circuit::scoped("Public", |scope| {
            let mut accumulator = zero;

            for i in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Public, accumulator);
                let b = Field::<Circuit>::new(Mode::Public, accumulator);
                let is_eq = a.is_eq(&b);
                assert_eq!(true, is_eq.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!((i + 1) * 2, scope.num_public_in_scope());
                assert_eq!((i + 1) * 2, scope.num_private_in_scope());
                assert_eq!((i + 1) * 3, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());

                accumulator = accumulator + &one;
            }
        });

        // Public and private variables
        Circuit::scoped("Public and Private", |scope| {
            let mut accumulator = zero;

            for i in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Public, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_eq(&b);
                assert_eq!(true, is_eq.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(i + 1, scope.num_public_in_scope());
                assert_eq!((i + 1) * 3, scope.num_private_in_scope());
                assert_eq!((i + 1) * 3, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());

                accumulator = accumulator + &one;
            }
        });

        // Private variables
        Circuit::scoped("Private", |scope| {
            let mut accumulator = zero;

            for i in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_eq(&b);
                assert_eq!(true, is_eq.to_value());
                assert!(scope.is_satisfied());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!((i + 1) * 4, scope.num_private_in_scope());
                assert_eq!((i + 1) * 3, scope.num_constraints_in_scope());

                accumulator = accumulator + &one;
            }
        });
    }

    #[test]
    fn test_is_neq_cases() {
        let zero = <Circuit as Environment>::BaseField::zero();
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;
        let five = two + two + one;

        // Inequality Enforcement
        // ----------------------------------------------------------------
        // Check 1:  (a - b) * multiplier = is_neq
        // Check 2:  (a - b) * not(is_neq) = 0

        let enforce = |a: Field<Circuit>, b: Field<Circuit>, multiplier: Field<Circuit>, is_neq: Boolean<Circuit>| {
            // Compute `self` - `other`.
            let delta = &a.0 - &b.0;

            // Negate `is_neq`.
            let is_eq = !is_neq.clone();

            // Check 1: (a - b) * multiplier = is_neq
            Circuit::enforce(|| (delta.clone(), multiplier, is_neq.clone()));

            // Check 2: (a - b) * not(is_neq) = 0
            Circuit::enforce(|| (delta, is_eq, Circuit::zero()));
        };

        //
        // Case 1: a == b AND is_neq == 0 (honest)
        // ----------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, five);
        let multiplier = Field::<Circuit>::new(Mode::Private, one);
        let is_neq = Boolean::new(Mode::Private, false);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(Circuit::is_satisfied());
        Circuit::reset_circuit();

        //
        // Case 2: a == b AND is_neq == 1 (dishonest)
        // ----------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, five);
        let multiplier = Field::<Circuit>::new(Mode::Private, one);
        let is_neq = Boolean::new(Mode::Private, true);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(!Circuit::is_satisfied());
        Circuit::reset_circuit();

        // Case 3a: a != b AND is_neq == 0 AND multiplier = 0 (dishonest)
        // ----------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, two);
        let multiplier = Field::<Circuit>::new(Mode::Private, zero);
        let is_neq = Boolean::new(Mode::Private, false);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(!Circuit::is_satisfied());
        Circuit::reset_circuit();

        //
        // Case 3b: a != b AND is_neq == 0 AND multiplier = 1 (dishonest)
        // ----------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, two);
        let multiplier = Field::<Circuit>::new(Mode::Private, one);
        let is_neq = Boolean::new(Mode::Private, false);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(!Circuit::is_satisfied());
        Circuit::reset_circuit();

        //
        // Case 4a: a != b AND is_neq == 1 AND multiplier = n [!= (a - b)^(-1)] (dishonest)
        // ---------------------------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, two);
        let multiplier = Field::<Circuit>::new(Mode::Private, two);
        let is_neq = Boolean::new(Mode::Private, true);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(!Circuit::is_satisfied());
        Circuit::reset_circuit();

        //
        // Case 4b: a != b AND is_neq == 1 AND multiplier = (a - b)^(-1) (honest)
        // ---------------------------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, two);
        let multiplier = Field::<Circuit>::new(
            Mode::Private,
            (five - two).inverse().expect("Failed to compute a native inverse"),
        );
        let is_neq = Boolean::new(Mode::Private, true);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(Circuit::is_satisfied());
        Circuit::reset_circuit();
    }
}
