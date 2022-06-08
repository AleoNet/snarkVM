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

impl<E: Environment> Div<Field<E>> for Field<E> {
    type Output = Field<E>;

    fn div(self, other: Field<E>) -> Self::Output {
        self / &other
    }
}

impl<E: Environment> Div<&Field<E>> for Field<E> {
    type Output = Field<E>;

    fn div(self, other: &Field<E>) -> Self::Output {
        &self / other
    }
}

impl<E: Environment> Div<Field<E>> for &Field<E> {
    type Output = Field<E>;

    fn div(self, other: Field<E>) -> Self::Output {
        self / &other
    }
}

impl<E: Environment> Div<&Field<E>> for &Field<E> {
    type Output = Field<E>;

    fn div(self, other: &Field<E>) -> Self::Output {
        let mut output = self.clone();
        output /= other;
        output
    }
}

impl<E: Environment> DivAssign<Self> for Field<E> {
    fn div_assign(&mut self, other: Self) {
        *self /= &other;
    }
}

impl<E: Environment> DivAssign<&Self> for Field<E> {
    fn div_assign(&mut self, other: &Self) {
        // If `other` is a constant, we can perform the multiplication and inversion
        // without paying for any private variables or constraints.
        if other.is_constant() {
            *self *= other.inverse();
        }
        // Otherwise, we can perform division with 1 constraint by using a `quotient` witness,
        // and ensuring that `quotient * other == self`.
        else {
            // Construct the quotient as a witness.
            let quotient = witness!(|self, other| self / other);

            // Ensure the quotient is correct by enforcing:
            // `quotient * other == self`.
            E::enforce(|| (&quotient, other, &*self));

            // Assign the quotient to `self`.
            *self = quotient;
        }
    }
}

impl<E: Environment> Metrics<dyn Div<Field<E>, Output = Field<E>>> for Field<E> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match case {
            (Mode::Constant, Mode::Constant) | (_, Mode::Constant) => Count::is(1, 0, 0, 0),
            (Mode::Constant, _) => Count::is(0, 0, 1, 1),
            (_, _) => Count::is(0, 0, 1, 1),
        }
    }
}

impl<E: Environment> OutputMode<dyn Div<Field<E>, Output = Field<E>>> for Field<E> {
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
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1000;

    fn check_div(
        name: &str,
        expected: &console::Field<<Circuit as Environment>::Network>,
        a: &Field<Circuit>,
        b: &Field<Circuit>,
    ) {
        Circuit::scope(name, || {
            let candidate = a / b;
            assert_eq!(*expected, candidate.eject_value(), "({} / {})", a.eject_value(), b.eject_value());
            assert_count!(Div(Field, Field) => Field, &(a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Div(Field, Field) => Field, &(CircuitType::from(a), CircuitType::from(b)), candidate);
        });
    }

    fn check_div_assign(
        name: &str,
        expected: &console::Field<<Circuit as Environment>::Network>,
        a: &Field<Circuit>,
        b: &Field<Circuit>,
    ) {
        Circuit::scope(name, || {
            let mut candidate = a.clone();
            candidate /= b;
            assert_eq!(*expected, candidate.eject_value(), "({} / {})", a.eject_value(), b.eject_value());
            assert_count!(Div(Field, Field) => Field, &(a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Div(Field, Field) => Field, &(CircuitType::from(a), CircuitType::from(b)), candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let expected = first / second;
            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, second);

            let name = format!("Div: a / b {}", i);
            check_div(&name, &expected, &a, &b);
            let name = format!("DivAssign: a / b {}", i);
            check_div_assign(&name, &expected, &a, &b);

            // Check division by one.
            let one = Field::<Circuit>::new(mode_b, console::Field::<<Circuit as Environment>::Network>::one());
            let name = format!("Div By One {}", i);
            check_div(&name, &first, &a, &one);
            let name = format!("DivAssign By One {}", i);
            check_div_assign(&name, &first, &a, &one);
        }
    }

    #[test]
    fn test_constant_div_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_div_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_div_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_div_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_public_div_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_div_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_div_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_private_div_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_div_private() {
        run_test(Mode::Private, Mode::Private);
    }

    #[test]
    fn test_div_by_zero_fails() {
        let zero = console::Field::<<Circuit as Environment>::Network>::zero();
        let one = console::Field::<<Circuit as Environment>::Network>::one();

        let result = std::panic::catch_unwind(|| Field::<Circuit>::one() / Field::zero());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result =
            std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Constant, one) / Field::new(Mode::Constant, zero));
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result =
            std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Public, one) / Field::new(Mode::Public, zero));
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result =
            std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Private, one) / Field::new(Mode::Private, zero));
        assert!(result.is_err()); // Probe further for specific error type here, if desired
    }
}
