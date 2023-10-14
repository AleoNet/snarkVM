// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use snarkvm_circuit_environment::Private;

impl<E: Environment> Equal<Self> for Field<E> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// This method costs 2 constraints.
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
    /// This method costs 2 constraints.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        // In all cases, the witness ("ejected") value is calculated from the ejected values.
        let is_neq_ejected = self.eject_value() != other.eject_value();

        match (self.is_constant(), other.is_constant()) {
            // If both operands are constant, the result is also constant.
            (true, true) => Boolean::new(Mode::Constant, is_neq_ejected),

            // Otherwise, we introduce a private field variable is_neq for the result,
            // along with an auxiliary variable multiplier for the inverse of the difference between the operands,
            // and enforce the following constraints:
            // 1.  (self - other) (multiplier) = (is_neq)
            // 2.  (self - other) (1 - is_neq) = (0)
            // These constraints imply that is_neq is boolean, i.e. either 0 or 1 (see below);
            // so we avoid creating is_neq as a Boolean, which would generate an unneeded boolean constraint.
            //
            // The specification of this circuit is the calculation of field inequality:
            //   is_neq = [IF self = other THEN 0 ELSE 1]
            // i.e. the result is_neq is 0 if the two operands are equal, 1 if they are not equal.
            //
            // The correctness of the circuit, i.e. its equivalence to the specification, is proved as follows.
            //
            // Soundness: the constraints imply the specification,
            // i.e. every solution of the constraints corresponds to a correct computation of field inequality.
            // - If self = other, constraint 1 implies is_neq = 0, consistently with the specification,
            // - If self != other, constraint 2 implies (1 - is_neq) = 0, i.e. is_neq = 1, consistently with the specification.
            //
            // Completeness: the specification implies the constraints,
            // i.e. the constraints are satisfiable for every correct computation of field inequality.
            // - If self = other, constraint 2 reduces to 0 = 0.
            //   The specification implies is_neq = 0, and constraint 1 reduces to 0 = 0,
            //   regardless of the choice of multiplier.
            // - If self != other, the specification implies is_neq = 1,
            //   which reduces constraint 2 to 0 = 0 and constraint 1 to (self - other) (multiplier) = 1,
            //   which is satisfied by choosing multiplier = 1 / (self - other),
            //   which is well-defined because (self - other) != 0.
            //
            // Thus the circuit is equivalent to the specification.
            // Since the specification implies that is_neq is either 0 or 1,
            // the circuit does not need a boolean constraint for is_neq, as mentioned above.
            _ => {

                // Allocate a new R1CS field variable for the result.
                // Its value is 1 if self and other are not equal, 0 if equal.
                let is_neq = Boolean::from_variable(E::new_variable(Mode::Private, match is_neq_ejected {
                    true => E::BaseField::one(),
                    false => E::BaseField::zero(),
                }));

                // Calculate a linear combination that is the difference of self and other.
                let delta = self - other;

                // Introduce an internal variable multiplier (see constraints above).
                // Its value is the inverse of self - other is they are not equal,
                // otherwise its value is irrelevant to the satisfaction of the constraints,
                // and we just pick 1 in that case.
                let multiplier: Field<E> = witness!(|delta| {
                    match delta.inverse() {
                        Ok(inverse) => inverse,
                        _ => console::Field::one(),
                    }
                });

                // Calculate is_eq = 1 - is_neq.
                let is_eq = !is_neq.clone();

                // Enforce 1st constraint (see above).
                E::enforce(|| (&delta, &multiplier, &is_neq));

                // Enforce 2nd constraint (see above).
                E::enforce(|| (delta, is_eq, E::zero()));

                // Return result.
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
            _ => Count::is(0, 0, 2, 2),
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
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, second);

            let name = format!("Equal: a == b {i}");
            check_is_equal(&name, first == second, &a, &b);

            let name = format!("Not Equal: a != b {i}");
            check_is_not_equal(&name, first != second, &a, &b);

            // Check first is equal to first.
            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, first);
            let name = format!("{first} == {first}");
            check_is_equal(&name, true, &a, &b);

            // Check second is equal to second.
            let a = Field::<Circuit>::new(mode_a, second);
            let b = Field::<Circuit>::new(mode_b, second);
            let name = format!("{second} == {second}");
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
