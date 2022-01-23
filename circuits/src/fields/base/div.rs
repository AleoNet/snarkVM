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

impl<E: Environment> Div<Self> for BaseField<E> {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment> Div<&Self> for BaseField<E> {
    type Output = Self;

    fn div(self, other: &Self) -> Self::Output {
        let mut output = self;
        output /= other;
        output
    }
}

impl<E: Environment> DivAssign<Self> for BaseField<E> {
    fn div_assign(&mut self, other: Self) {
        *self /= &other;
    }
}

impl<E: Environment> DivAssign<&Self> for BaseField<E> {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, other: &Self) {
        *self *= other.inv();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 25;

    fn check_div(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        let one = <Circuit as Environment>::BaseField::one();

        let mut dividend = one;
        for i in 0..ITERATIONS {
            let mut divisor = one;
            for j in 0..ITERATIONS {
                let a = BaseField::<Circuit>::new(mode_a, dividend);
                let b = BaseField::new(mode_b, divisor);

                Circuit::scoped(&format!("{:?} / {:?} - ({}, {})", mode_a, mode_b, i, j), |scope| {
                    let expected_quotient = dividend / divisor;
                    let candidate_quotient = a / b;
                    assert_eq!(expected_quotient, candidate_quotient.eject_value());

                    assert_eq!(num_constants, scope.num_constants_in_scope(), "(num_constants)");
                    assert_eq!(num_public, scope.num_public_in_scope(), "(num_public)");
                    assert_eq!(num_private, scope.num_private_in_scope(), "(num_private)");
                    assert_eq!(num_constraints, scope.num_constraints_in_scope(), "(num_constraints)");
                    assert!(Circuit::is_satisfied(), "(is_satisfied)");

                    divisor += one;
                });
            }
            dividend += one;
        }
    }

    #[test]
    fn test_constant_div_constant() {
        check_div(Mode::Constant, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_constant_div_public() {
        check_div(Mode::Constant, Mode::Public, 0, 0, 1, 1);
    }

    #[test]
    fn test_constant_div_private() {
        check_div(Mode::Constant, Mode::Private, 0, 0, 1, 1);
    }

    #[test]
    fn test_public_div_constant() {
        check_div(Mode::Public, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_public_div_public() {
        check_div(Mode::Public, Mode::Public, 0, 0, 2, 2);
    }

    #[test]
    fn test_public_div_private() {
        check_div(Mode::Public, Mode::Private, 0, 0, 2, 2);
    }

    #[test]
    fn test_private_div_constant() {
        check_div(Mode::Private, Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_private_div_public() {
        check_div(Mode::Private, Mode::Public, 0, 0, 2, 2);
    }

    #[test]
    fn test_private_div_private() {
        check_div(Mode::Private, Mode::Private, 0, 0, 2, 2);
    }

    #[test]
    fn test_div_by_zero_fails() {
        let zero = <Circuit as Environment>::BaseField::zero();
        let one = <Circuit as Environment>::BaseField::one();

        let result = std::panic::catch_unwind(|| BaseField::<Circuit>::one() / BaseField::zero());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| {
            BaseField::<Circuit>::new(Mode::Constant, one) / BaseField::new(Mode::Constant, zero)
        });
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| {
            BaseField::<Circuit>::new(Mode::Public, one) / BaseField::new(Mode::Public, zero)
        });
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| {
            BaseField::<Circuit>::new(Mode::Private, one) / BaseField::new(Mode::Private, zero)
        });
        assert!(result.is_err()); // Probe further for specific error type here, if desired
    }
}
