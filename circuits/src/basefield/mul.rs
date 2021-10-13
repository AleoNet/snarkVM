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

impl<E: Environment> Mul<BaseField<E>> for BaseField<E> {
    type Output = BaseField<E>;

    fn mul(self, other: BaseField<E>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<BaseField<E>> for &BaseField<E> {
    type Output = BaseField<E>;

    fn mul(self, other: BaseField<E>) -> Self::Output {
        other * self
    }
}

impl<E: Environment> Mul<&BaseField<E>> for BaseField<E> {
    type Output = BaseField<E>;

    fn mul(self, other: &BaseField<E>) -> Self::Output {
        &self * other
    }
}

impl<E: Environment> Mul<&BaseField<E>> for &BaseField<E> {
    type Output = BaseField<E>;

    fn mul(self, other: &BaseField<E>) -> Self::Output {
        let mut output = (*self).clone();
        output *= other;
        output
    }
}

impl<E: Environment> MulAssign<BaseField<E>> for BaseField<E> {
    fn mul_assign(&mut self, other: BaseField<E>) {
        *self *= &other;
    }
}

impl<E: Environment> MulAssign<&BaseField<E>> for BaseField<E> {
    fn mul_assign(&mut self, other: &BaseField<E>) {
        match (self.is_constant(), other.is_constant()) {
            (true, true) => *self = Self::new(Mode::Constant, self.eject_value() * other.eject_value()),
            (true, false) => self.0 = other.0.clone() * self.eject_value(),
            (false, true) => self.0 = self.0.clone() * other.eject_value(),
            (false, false) => {
                let product = BaseField::new(Mode::Private, self.eject_value() * other.eject_value());

                // Ensure self * other == product.
                E::enforce(|| (self.0.clone(), other, &product));

                *self = product;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 500;

    #[test]
    fn test_mul() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        // Constant * Constant
        Circuit::scoped("Constant * Constant", |scope| {
            let mut candidate_product = BaseField::<Circuit>::one();
            let mut expected_product = one;

            for i in 0..ITERATIONS {
                candidate_product = candidate_product * BaseField::new(Mode::Constant, two);
                expected_product = expected_product * &two;

                assert_eq!((i + 1) * 2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }

            assert_eq!(expected_product, candidate_product.eject_value());
        });

        // Constant * Public
        Circuit::scoped("Constant * Public", |scope| {
            let mut candidate_product = BaseField::<Circuit>::one();
            let mut expected_product = one;

            for i in 0..ITERATIONS {
                candidate_product =
                    BaseField::new(Mode::Constant, expected_product) * BaseField::new(Mode::Public, two);
                expected_product = expected_product * &two;

                assert_eq!(i + 1, scope.num_constants_in_scope());
                assert_eq!(i + 1, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }

            assert_eq!(expected_product, candidate_product.eject_value());
        });

        // Public * Constant
        Circuit::scoped("Public * Constant", |scope| {
            let mut candidate_product = BaseField::<Circuit>::one();
            let mut expected_product = one;

            for i in 0..ITERATIONS {
                candidate_product =
                    BaseField::new(Mode::Public, expected_product) * BaseField::new(Mode::Constant, two);
                expected_product = expected_product * &two;

                assert_eq!(i + 1, scope.num_constants_in_scope());
                assert_eq!(i + 1, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }

            assert_eq!(expected_product, candidate_product.eject_value());
        });

        // Public * Public
        Circuit::scoped("Public * Public", |scope| {
            let mut candidate_product = BaseField::<Circuit>::new(Mode::Public, one);
            let mut expected_product = one;

            for i in 0..ITERATIONS {
                candidate_product = candidate_product * BaseField::new(Mode::Public, two);
                expected_product = expected_product * &two;

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(i + 2, scope.num_public_in_scope());
                assert_eq!(i + 1, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            }

            assert_eq!(expected_product, candidate_product.eject_value());
        });

        // Private * Private
        Circuit::scoped("Private * Private", |scope| {
            let mut candidate_product = BaseField::<Circuit>::new(Mode::Private, one);
            let mut expected_product = one;

            for i in 0..ITERATIONS {
                candidate_product = candidate_product * BaseField::new(Mode::Private, two);
                expected_product = expected_product * &two;

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(i * 2 + 3, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            }

            assert_eq!(expected_product, candidate_product.eject_value());
        });
    }

    #[test]
    fn test_0_times_0() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = BaseField::<Circuit>::zero() * BaseField::zero();
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::zero() * &BaseField::zero();
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Public, zero) * BaseField::new(Mode::Public, zero);
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Public, zero) * BaseField::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Private, zero) * BaseField::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_0_times_1() {
        let zero = <Circuit as Environment>::BaseField::zero();
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = BaseField::<Circuit>::zero() * BaseField::one();
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::zero() * &BaseField::one();
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::one() * BaseField::zero();
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::one() * &BaseField::zero();
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Public, one) * BaseField::new(Mode::Public, zero);
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Public, one) * BaseField::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Private, one) * BaseField::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_1_times_1() {
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = BaseField::<Circuit>::one() * BaseField::one();
        assert_eq!(one, candidate.eject_value());

        let candidate = BaseField::<Circuit>::one() * &BaseField::one();
        assert_eq!(one, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Public, one) * BaseField::new(Mode::Public, one);
        assert_eq!(one, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Private, one) * BaseField::new(Mode::Public, one);
        assert_eq!(one, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Private, one) * BaseField::new(Mode::Private, one);
        assert_eq!(one, candidate.eject_value());
    }

    #[test]
    fn test_2_times_2() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;
        let four = two + two;

        let candidate_two = BaseField::<Circuit>::one() + BaseField::one();
        let candidate = candidate_two * (BaseField::<Circuit>::one() + BaseField::one());
        assert_eq!(four, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Public, two) * BaseField::new(Mode::Public, two);
        assert_eq!(four, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Private, two) * BaseField::new(Mode::Public, two);
        assert_eq!(four, candidate.eject_value());

        let candidate = BaseField::<Circuit>::new(Mode::Private, two) * BaseField::new(Mode::Private, two);
        assert_eq!(four, candidate.eject_value());
    }
}
