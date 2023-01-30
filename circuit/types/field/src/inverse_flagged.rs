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

impl<E: Environment> InverseFlagged for Field<E> {
    type Output = (Field<E>, Boolean<E>);

    fn inverse_flagged(&self) -> Self::Output {
        let inverse = witness!(|self| match self.inverse() {
            Ok(inverse) => inverse,
            _ => console::Field::zero(),
        });

        // If `self` is not zero, ensure that the inverse is well formed, that is `self` * `self^(-1)` == 1.
        // This is equivalent to `!self_is_zero ==> (self * inverse == E::one())`.
        // Which is equivalent to `self_is_zero || (self * inverse == E::one())`.
        let self_is_zero = self.is_zero();
        let self_times_inverse_equals_one = (self * &inverse).is_equal(&Self::one());
        E::assert((&self_is_zero).bitor(&self_times_inverse_equals_one));

        (inverse, self_is_zero)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1_000;

    fn check_inverse(name: &str, mode: Mode, rng: &mut TestRng) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let element: console::Field<<Circuit as Environment>::Network> = Uniform::rand(rng);
            // Compute it's inverse, or skip this iteration if it does not natively exist.
            match element.inverse() {
                Ok(expected) => {
                    // Check that `inverse_flagged` produces the correct result.
                    let a = Field::<Circuit>::new(mode, element);
                    Circuit::scope(name, || {
                        let (result, flag) = a.inverse_flagged();
                        assert_eq!(result.eject_value(), expected);
                        assert!(!flag.eject_value());
                        assert!(Circuit::is_satisfied(), "(is_satisfied_in_scope)");
                    });
                    Circuit::reset();

                    // Check that `inverse` matches `inverse_flagged`.
                    Circuit::scope(name, || {
                        let result = a.inverse();
                        assert_eq!(result.eject_value(), expected);
                        assert!(Circuit::is_satisfied(), "(is_satisfied_in_scope)");
                    });
                    Circuit::reset();
                }
                Err(_) => {
                    // Check that `inverse_flagged` produces the correct result.
                    let a = Field::<Circuit>::new(mode, element);
                    Circuit::scope(name, || {
                        let (result, flag) = a.inverse_flagged();
                        assert_eq!(result.eject_value(), console::Field::zero());
                        assert!(flag.eject_value());
                        assert!(Circuit::is_satisfied(), "(is_satisfied_in_scope)");
                    });
                    Circuit::reset();

                    // Check that `inverse` halts or that the circuit is not satisfied.
                    match mode {
                        Mode::Constant => {
                            let result = std::panic::catch_unwind(|| a.inverse_flagged());
                            assert!(result.is_err());
                        }
                        _ => {
                            Circuit::scope(name, || {
                                let _ = a.inverse();
                                assert!(!Circuit::is_satisfied(), "(!is_satisfied_in_scope)");
                            });
                            Circuit::reset();
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_inverse() {
        let mut rng = TestRng::default();

        check_inverse("Constant", Mode::Constant, &mut rng);
        check_inverse("Public", Mode::Public, &mut rng);
        check_inverse("Private", Mode::Private, &mut rng);
    }

    #[test]
    fn test_zero_inverse_fails() {
        let zero = console::Field::<<Circuit as Environment>::Network>::zero();

        let result = std::panic::catch_unwind(|| Field::<Circuit>::zero().inverse());
        assert!(result.is_err());
        Circuit::reset();

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Constant, zero).inverse());
        assert!(result.is_err());
        Circuit::reset();

        let candidate = Field::<Circuit>::new(Mode::Public, zero).inverse();
        assert_eq!(zero, candidate.eject_value());
        assert!(!Circuit::is_satisfied());
        Circuit::reset();

        let candidate = Field::<Circuit>::new(Mode::Private, zero).inverse();
        assert_eq!(zero, candidate.eject_value());
        assert!(!Circuit::is_satisfied());
        Circuit::reset();
    }
}
