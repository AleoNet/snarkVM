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

impl<E: Environment> Equal<Self> for Field<E> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// This method costs 3 constraints.
    ///
    fn is_equal(&self, other: &Self) -> Self::Output {
        !self.is_not_equal(other)
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    /// This method costs 3 constraints.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        match (self.is_constant(), other.is_constant()) {
            (true, true) => witness!(|self, other| self != other),
            _ => {
                // Compute a boolean that is `true` if `this` and `that` are not equivalent.
                let is_neq: Boolean<E> = witness!(|self, other| self != other);

                // Assign the expected multiplier.
                let multiplier: Field<E> = witness!(|self, other| {
                    match (self - other).inverse() {
                        Ok(inverse) => inverse,
                        _ => console::Field::one(),
                    }
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
                let delta = self - other;

                // Negate `is_neq`.
                let is_eq = !is_neq.clone();

                // Check 1: (a - b) * multiplier = is_neq
                E::enforce(|| (&delta, &multiplier, &is_neq));

                // Check 2: (a - b) * not(is_neq) = 0
                E::enforce(|| (delta, is_eq, E::zero()));

                is_neq
            }
        }
    }
}

impl<E: Environment> Metrics<dyn Equal<Field<E>, Output = Boolean<E>>> for Field<E> {
    type Case = (Mode, Mode);

    // TODO: How to deal where both operands are the same field element, since it changes the number of gates produced? We could use upper bounds.
    fn count(case: &Self::Case) -> Count {
        match case {
            (Mode::Constant, Mode::Constant) => Count::is(1, 0, 0, 0),
            _ => Count::is(0, 0, 2, 3),
        }
    }
}

impl<E: Environment> OutputMode<dyn Equal<Field<E>, Output = Boolean<E>>> for Field<E> {
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match case {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 200;

    fn check_is_equal(name: &str, expected: bool, a: &Field<Circuit>, b: &Field<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.is_equal(b);
            assert_eq!(expected, candidate.eject_value(), "({} == {})", a.eject_value(), b.eject_value());
            assert_count!(Equal(Field, Field) => Boolean, &(a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Equal(Field, Field) => Boolean, &(a.eject_mode(), b.eject_mode()), candidate);
        });
    }

    fn check_is_not_equal(name: &str, expected: bool, a: &Field<Circuit>, b: &Field<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.is_not_equal(b);
            assert_eq!(expected, candidate.eject_value(), "({} != {})", a.eject_value(), b.eject_value());
            assert_count!(Equal(Field, Field) => Boolean, &(a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Equal(Field, Field) => Boolean, &(a.eject_mode(), b.eject_mode()), candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, second);

            let name = format!("Equal: a == b {}", i);
            check_is_equal(&name, first == second, &a, &b);

            let name = format!("Not Equal: a != b {}", i);
            check_is_not_equal(&name, first != second, &a, &b);

            // Check first is equal to first.
            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, first);
            let name = format!("{} == {}", first, first);
            check_is_equal(&name, true, &a, &b);

            // Check second is equal to second.
            let a = Field::<Circuit>::new(mode_a, second);
            let b = Field::<Circuit>::new(mode_b, second);
            let name = format!("{} == {}", second, second);
            check_is_equal(&name, true, &a, &b);
        }
    }

    #[test]
    fn test_constant_is_equal_to_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_is_not_equal_to_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_is_not_equal_to_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_is_equal_to_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_private_is_equal_to_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_public_is_equal_to_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_is_not_equal_to_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_is_equal_to_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_is_equal_to_private() {
        run_test(Mode::Private, Mode::Private);
    }

    #[test]
    fn test_is_eq_cases() {
        let one = console::Field::<<Circuit as Environment>::Network>::one();

        // Basic `true` and `false` cases
        {
            let mut accumulator = one + one;

            for _ in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_equal(&b);
                assert!(is_eq.eject_value()); // true

                let a = Field::<Circuit>::new(Mode::Private, one);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_equal(&b);
                assert!(!is_eq.eject_value()); // false

                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator - one);
                let is_eq = a.is_equal(&b);
                assert!(!is_eq.eject_value()); // false

                accumulator += one;
            }
        }
    }

    #[test]
    fn test_is_neq_cases() {
        let zero = console::Field::<<Circuit as Environment>::Network>::zero();
        let one = console::Field::<<Circuit as Environment>::Network>::one();
        let two = one + one;
        let five = two + two + one;

        // Inequality Enforcement
        // ----------------------------------------------------------------
        // Check 1:  (a - b) * multiplier = is_neq
        // Check 2:  (a - b) * not(is_neq) = 0

        let enforce = |a: Field<Circuit>, b: Field<Circuit>, multiplier: Field<Circuit>, is_neq: Boolean<Circuit>| {
            // Compute `self` - `other`.
            let delta = &a - &b;

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
        Circuit::reset();

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
        Circuit::reset();

        // Case 3a: a != b AND is_neq == 0 AND multiplier = 0 (dishonest)
        // ----------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, two);
        let multiplier = Field::<Circuit>::new(Mode::Private, zero);
        let is_neq = Boolean::new(Mode::Private, false);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(!Circuit::is_satisfied());
        Circuit::reset();

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
        Circuit::reset();

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
        Circuit::reset();

        //
        // Case 4b: a != b AND is_neq == 1 AND multiplier = (a - b)^(-1) (honest)
        // ---------------------------------------------------------------------------------

        let a = Field::<Circuit>::new(Mode::Private, five);
        let b = Field::<Circuit>::new(Mode::Private, two);
        let multiplier =
            Field::<Circuit>::new(Mode::Private, (five - two).inverse().expect("Failed to compute a native inverse"));
        let is_neq = Boolean::new(Mode::Private, true);

        assert!(Circuit::is_satisfied());
        enforce(a, b, multiplier, is_neq);
        assert!(Circuit::is_satisfied());
        Circuit::reset();
    }
}
