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

impl<E: Environment> Div<Self> for Field<E> {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment> Div<&Self> for Field<E> {
    type Output = Self;

    fn div(self, other: &Self) -> Self::Output {
        let mut output = self;
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
        *self *= other.inv();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 500;

    #[test]
    fn test_div() {
        let one = <Circuit as Environment>::Field::one();

        // Constant variables
        let mut dividend = one;
        for i in 0..ITERATIONS {
            let mut divisor = one;
            for j in 0..ITERATIONS {
                Circuit::scoped(&format!("Constant - ({}, {})", i, j), |scope| {
                    let expected_quotient = dividend / divisor;
                    let candidate_quotient =
                        Field::<Circuit>::new(Mode::Constant, dividend) / Field::new(Mode::Constant, divisor);
                    assert_eq!(expected_quotient, candidate_quotient.to_value());

                    assert_eq!(4, scope.num_constants_in_scope());
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
                        Field::<Circuit>::new(Mode::Public, dividend) / Field::new(Mode::Public, divisor);
                    assert_eq!(expected_quotient, candidate_quotient.to_value());

                    assert_eq!(0, scope.num_constants_in_scope());
                    assert_eq!(2, scope.num_public_in_scope());
                    assert_eq!(2, scope.num_private_in_scope());
                    assert_eq!(2, scope.num_constraints_in_scope());

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
                        Field::<Circuit>::new(Mode::Private, dividend) / Field::new(Mode::Private, divisor);
                    assert_eq!(expected_quotient, candidate_quotient.to_value());

                    assert_eq!(0, scope.num_constants_in_scope());
                    assert_eq!(0, scope.num_public_in_scope());
                    assert_eq!(4, scope.num_private_in_scope());
                    assert_eq!(2, scope.num_constraints_in_scope());

                    divisor += one;
                });
            }
            dividend += one;
        }
    }

    #[test]
    fn test_div_by_zero_fails() {
        let zero = <Circuit as Environment>::Field::zero();
        let one = <Circuit as Environment>::Field::one();

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
