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

    #[test]
    fn test_div() {
        let one = <Circuit as Environment>::BaseField::one();

        // Constant variables
        let mut dividend = one;
        for i in 0..ITERATIONS {
            let mut divisor = one;
            for j in 0..ITERATIONS {
                Circuit::scoped(&format!("Constant - ({}, {})", i, j), |scope| {
                    let expected_quotient = dividend / divisor;
                    let candidate_quotient =
                        BaseField::<Circuit>::new(Mode::Constant, dividend) / BaseField::new(Mode::Constant, divisor);
                    assert_eq!(expected_quotient, candidate_quotient.eject_value());

                    assert_eq!(3, scope.num_constants_in_scope());
                    assert_eq!(0, scope.num_public_in_scope());
                    assert_eq!(0, scope.num_private_in_scope());
                    assert_eq!(0, scope.num_constraints_in_scope());

                    divisor += one;
                });
            }
            dividend += one;
        }

        // Public variables
        let mut dividend = one;
        for i in 0..ITERATIONS {
            let mut divisor = one;
            for j in 0..ITERATIONS {
                Circuit::scoped(&format!("Public - ({}, {})", i, j), |scope| {
                    let expected_quotient = dividend / divisor;
                    let candidate_quotient =
                        BaseField::<Circuit>::new(Mode::Public, dividend) / BaseField::new(Mode::Public, divisor);
                    assert_eq!(expected_quotient, candidate_quotient.eject_value());

                    assert_eq!(0, scope.num_constants_in_scope());
                    assert_eq!(2, scope.num_public_in_scope());
                    assert_eq!(2, scope.num_private_in_scope());
                    assert_eq!(2, scope.num_constraints_in_scope());
                    assert!(scope.is_satisfied());

                    divisor += one;
                });
            }
            dividend += one;
        }

        // Private variables
        let mut dividend = one;
        for i in 0..ITERATIONS {
            let mut divisor = one;
            for j in 0..ITERATIONS {
                Circuit::scoped(&format!("Private - ({}, {})", i, j), |scope| {
                    let expected_quotient = dividend / divisor;
                    let candidate_quotient =
                        BaseField::<Circuit>::new(Mode::Private, dividend) / BaseField::new(Mode::Private, divisor);
                    assert_eq!(expected_quotient, candidate_quotient.eject_value());

                    assert_eq!(0, scope.num_constants_in_scope());
                    assert_eq!(0, scope.num_public_in_scope());
                    assert_eq!(4, scope.num_private_in_scope());
                    assert_eq!(2, scope.num_constraints_in_scope());
                    assert!(scope.is_satisfied());

                    divisor += one;
                });
            }
            dividend += one;
        }
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
