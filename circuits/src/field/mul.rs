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

impl<E: Environment> Mul<Self> for Field<E> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<&Self> for Field<E> {
    type Output = Self;

    fn mul(self, other: &Self) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&Field<E>> for &Field<E> {
    type Output = Field<E>;

    fn mul(self, other: &Field<E>) -> Self::Output {
        let mut output = (*self).clone();
        output *= other;
        output
    }
}

impl<E: Environment> MulAssign<Self> for Field<E> {
    fn mul_assign(&mut self, other: Self) {
        *self *= &other;
    }
}

impl<E: Environment> MulAssign<&Self> for Field<E> {
    fn mul_assign(&mut self, other: &Self) {
        match (self.is_constant(), other.is_constant()) {
            (true, true) => *self = Self::new(Mode::Constant, self.to_value() * other.to_value()),
            (true, false) => self.0 = other.0.clone() * self.to_value(),
            (false, true) => self.0 = self.0.clone() * other.to_value(),
            (false, false) => {
                let product = E::new_variable(Mode::Private, self.to_value() * other.to_value());

                // Ensure self * other == product.
                E::enforce(|| (self.0.clone(), other, product));

                self.0 = product.into();
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
    fn test_mul() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        // Constant * Constant
        Circuit::scoped("Constant * Constant", |scope| {
            let mut expected_product = one;
            let mut candidate_product = Field::<Circuit>::one();

            for i in 0..ITERATIONS {
                expected_product = expected_product * &two;
                candidate_product = candidate_product * Field::new(Mode::Constant, two);

                assert_eq!((i + 1) * 2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }

            assert_eq!(expected_product, candidate_product.to_value());
        });

        // Public * Public
        Circuit::scoped("Public * Public", |scope| {
            let mut expected_product = one;
            let mut candidate_product = Field::<Circuit>::new(Mode::Public, one);

            for i in 0..ITERATIONS {
                expected_product = expected_product * &two;
                candidate_product = candidate_product * Field::new(Mode::Public, two);

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(i + 2, scope.num_public_in_scope());
                assert_eq!(i + 1, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            }

            assert_eq!(expected_product, candidate_product.to_value());
        });

        // Private * Private
        Circuit::scoped("Private * Private", |scope| {
            let mut expected_product = one;
            let mut candidate_product = Field::<Circuit>::new(Mode::Private, one);

            for i in 0..ITERATIONS {
                expected_product = expected_product * &two;
                candidate_product = candidate_product * Field::new(Mode::Private, two);

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(i * 2 + 3, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            }

            assert_eq!(expected_product, candidate_product.to_value());
        });
    }

    #[test]
    fn test_0_times_0() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = Field::<Circuit>::zero() * Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::zero() * &Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, zero) * Field::new(Mode::Public, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, zero) * Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, zero) * Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_0_times_1() {
        let zero = <Circuit as Environment>::BaseField::zero();
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = Field::<Circuit>::zero() * Field::one();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::zero() * &Field::one();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::one() * Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::one() * &Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one) * Field::new(Mode::Public, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one) * Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one) * Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_1_times_1() {
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = Field::<Circuit>::one() * Field::one();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::one() * &Field::one();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one) * Field::new(Mode::Public, one);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one) * Field::new(Mode::Public, one);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one) * Field::new(Mode::Private, one);
        assert_eq!(one, candidate.to_value());
    }

    #[test]
    fn test_2_times_2() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;
        let four = two + two;

        let candidate_two = Field::<Circuit>::one() + Field::one();
        let candidate = candidate_two * (Field::<Circuit>::one() + Field::one());
        assert_eq!(four, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, two) * Field::new(Mode::Public, two);
        assert_eq!(four, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, two) * Field::new(Mode::Public, two);
        assert_eq!(four, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, two) * Field::new(Mode::Private, two);
        assert_eq!(four, candidate.to_value());
    }
}
