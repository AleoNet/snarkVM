// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<E: Environment> DivFlagged<Field<E>> for Field<E> {
    type Output = (Field<E>, Boolean<E>);

    /// Performs flagged division of two field elements.
    #[doc(hidden)]
    fn div_flagged(&self, other: &Field<E>) -> Self::Output {
        match other.is_constant() {
            // If `other` is a constant and zero, return the zero element and set the flag.
            true if other.eject_value().is_zero() => (Field::zero(), Boolean::constant(true)),
            // If `other` is a constant and non-zero, we can perform multiplication and inversion for 0 constraints.
            // If `self` is a constant, we can perform multiplication and inversion for 1 constraint.
            // Otherwise, we can perform multiplication and inversion for 2 constraints.
            _ => {
                let (other_inverse, flag) = other.inverse_flagged();
                (self * other_inverse, flag)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1000;

    fn check_div_flagged(
        name: &str,
        first: &console::Field<<Circuit as Environment>::Network>,
        second: &console::Field<<Circuit as Environment>::Network>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = &Field::<Circuit>::new(mode_a, *first);
        let b = &Field::<Circuit>::new(mode_b, *second);

        match second.is_zero() {
            true => {
                // Check that `div_flagged` produces the correct result and that the flag is set.
                Circuit::scope(name, || {
                    let (result, flag) = a.div_flagged(b);
                    assert_eq!(result.eject_value(), console::Field::zero());
                    assert!(flag.eject_value());
                });
                Circuit::reset();

                // Check that `div` produces the correct result.
                match mode_b.is_constant() {
                    true => {
                        // Check that `div` halts.
                        let result = std::panic::catch_unwind(|| a.div(b));
                        assert!(result.is_err());
                    }
                    false => {
                        // Check that the circuit is not satisfied.
                        Circuit::scope(name, || {
                            let _ = a.div(b);
                            assert!(!Circuit::is_satisfied_in_scope(), "(!is_satisfied_in_scope)")
                        });
                        Circuit::reset();
                    }
                }
            }
            false => {
                let expected = *first / *second;
                // Check that `div_flagged` produces the correct result and that the flag is unset.
                Circuit::scope(name, || {
                    let (candidate_result, candidate_flag) = a.div_flagged(b);
                    assert_eq!(expected, candidate_result.eject_value(), "({} / {})", a.eject_value(), b.eject_value());
                    assert!(!candidate_flag.eject_value());
                    assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)")
                });
                Circuit::reset();

                // Check that `div` produces the same result as `div_flagged`.
                Circuit::scope(name, || {
                    let candidate_result = a.div(b);
                    assert_eq!(expected, candidate_result.eject_value(), "({} / {})", a.eject_value(), b.eject_value());
                    assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)")
                });
            }
        }
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("Div: a / b {}", i);
            check_div_flagged(&name, &first, &second, mode_a, mode_b);

            // Check division by one.
            let one = console::Field::<<Circuit as Environment>::Network>::one();
            let name = format!("Div By One {}", i);
            check_div_flagged(&name, &first, &one, mode_a, mode_b);

            // Check division by zero.
            let zero = console::Field::<<Circuit as Environment>::Network>::zero();
            let name = format!("Div By Zero {}", i);
            check_div_flagged(&name, &first, &zero, mode_a, mode_b);
        }
    }

    #[test]
    fn test_constant_div_flagged_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_div_flagged_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_div_flagged_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_div_flagged_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_public_div_flagged_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_div_flagged_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_div_flagged_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_private_div_flagged_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_div_flagged_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
