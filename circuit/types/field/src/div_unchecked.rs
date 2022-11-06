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

impl<E: Environment> DivUnchecked<Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Performs unchecked division of two field elements.
    /// This method does **not** enforce the case of `0 / 0`.
    #[doc(hidden)]
    fn div_unchecked(&self, other: &Field<E>) -> Self::Output {
        match (self.is_constant(), other.is_constant()) {
            // If `other` is a constant and zero, halt since the inverse of zero is undefined.
            (_, true) if other.eject_value().is_zero() => E::halt("Attempted to divide by zero."),
            // If `other` is a constant and non-zero, we can perform the multiplication and inversion
            // without paying for any private variables or constraints.
            // If `self` is a constant, we can perform the multiplication and inversion for 1 constraint.
            (_, true) | (true, false) => self * other.inverse(),
            // Otherwise, we can perform division with 1 constraint by using a `quotient` witness,
            // and ensuring that `quotient * other == self`.
            (false, false) => {
                // Construct the quotient as a witness.
                let quotient: Field<E> = witness!(|self, other| {
                    // Note: This band-aid was added to prevent a panic when `other` is zero.
                    let other = if other.is_zero() { console::Field::one() } else { other };
                    self / other
                });

                // Ensure the quotient is correct by enforcing:
                // `quotient * other == self`.
                E::enforce(|| (&quotient, other, self));

                // Return the quotient.
                quotient
            }
        }
    }
}

impl<E: Environment> Metrics<dyn DivUnchecked<Field<E>, Output = Field<E>>> for Field<E> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match case {
            (Mode::Constant, Mode::Constant) | (_, Mode::Constant) => Count::is(1, 0, 0, 0),
            (_, _) => Count::is(0, 0, 1, 1),
        }
    }
}

impl<E: Environment> OutputMode<dyn DivUnchecked<Field<E>, Output = Field<E>>> for Field<E> {
    type Case = (CircuitType<Field<E>>, CircuitType<Field<E>>);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0.mode(), case.1.mode()) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (Mode::Public, Mode::Constant) => match &case.1 {
                CircuitType::Constant(constant) => match constant.eject_value().is_one() {
                    true => Mode::Public,
                    false => Mode::Private,
                },
                _ => E::halt("The constant is required to determine the output mode of Public + Constant"),
            },
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::{assert_count_fails, Circuit};

    const ITERATIONS: u64 = 1000;

    fn check_div_unchecked(
        name: &str,
        first: &console::Field<<Circuit as Environment>::Network>,
        second: &console::Field<<Circuit as Environment>::Network>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = &Field::<Circuit>::new(mode_a, *first);
        let b = &Field::<Circuit>::new(mode_b, *second);

        match second.is_zero() {
            true => match mode_b.is_constant() {
                true => {
                    let result = std::panic::catch_unwind(|| a.div_unchecked(b));
                    assert!(result.is_err());
                }
                false => {
                    Circuit::scope(name, || {
                        let _ = a.div_unchecked(b);
                        assert_count_fails!(DivUnchecked(Field, Field) => Field, &(a.eject_mode(), b.eject_mode()));
                    });
                }
            },
            false => {
                let expected = *first / *second;
                Circuit::scope(name, || {
                    let candidate = a.div_unchecked(b);
                    assert_eq!(expected, candidate.eject_value(), "({} / {})", a.eject_value(), b.eject_value());
                    assert_count!(DivUnchecked(Field, Field) => Field, &(a.eject_mode(), b.eject_mode()));
                    assert_output_mode!(DivUnchecked(Field, Field) => Field, &(CircuitType::from(a), CircuitType::from(b)), candidate);
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
            check_div_unchecked(&name, &first, &second, mode_a, mode_b);

            // Check division by one.
            let one = console::Field::<<Circuit as Environment>::Network>::one();
            let name = format!("Div By One {}", i);
            check_div_unchecked(&name, &first, &one, mode_a, mode_b);

            // Check division by zero.
            let zero = console::Field::<<Circuit as Environment>::Network>::zero();
            let name = format!("Div By Zero {}", i);
            check_div_unchecked(&name, &first, &zero, mode_a, mode_b);
        }
    }

    #[test]
    fn test_constant_div_unchecked_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_div_unchecked_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_div_unchecked_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_div_unchecked_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_public_div_unchecked_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_div_unchecked_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_div_unchecked_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_private_div_unchecked_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_div_unchecked_private() {
        run_test(Mode::Private, Mode::Private);
    }

    #[test]
    fn test_div_unchecked_by_zero_fails() {
        let zero = console::Field::<<Circuit as Environment>::Network>::zero();
        let one = console::Field::<<Circuit as Environment>::Network>::one();

        let result = std::panic::catch_unwind(|| Field::<Circuit>::one() / Field::zero());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result =
            std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Constant, one) / Field::new(Mode::Constant, zero));
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        Circuit::scope("Public Div by Zero", || {
            let _ = Field::<Circuit>::new(Mode::Public, one) / Field::new(Mode::Public, zero);
            assert!(!Circuit::is_satisfied_in_scope());
        });

        Circuit::scope("Private Div by Zero", || {
            let _ = Field::<Circuit>::new(Mode::Private, one) / Field::new(Mode::Private, zero);
            assert!(!Circuit::is_satisfied_in_scope());
        });
    }
}
