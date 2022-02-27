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
            (true, true) => self.0 = self.0.clone() * other.eject_value(),
            (false, true) => self.0 = self.0.clone() * other.eject_value(),
            (true, false) => self.0 = other.0.clone() * self.eject_value(),
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
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 10;

    fn check_mul(
        name: &str,
        expected: &<Circuit as Environment>::BaseField,
        a: &BaseField<Circuit>,
        b: &BaseField<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = a * b;
            assert_eq!(*expected, candidate.eject_value(), "({} * {})", a.eject_value(), b.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    fn check_mul_assign(
        name: &str,
        expected: &<Circuit as Environment>::BaseField,
        a: &BaseField<Circuit>,
        b: &BaseField<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let mut candidate = a.clone();
            candidate *= b;
            assert_eq!(*expected, candidate.eject_value(), "({} * {})", a.eject_value(), b.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_constant_times_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Constant, first);
            let b = BaseField::<Circuit>::new(Mode::Constant, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_times_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Constant, first);
            let b = BaseField::<Circuit>::new(Mode::Public, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_times_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Constant, first);
            let b = BaseField::<Circuit>::new(Mode::Private, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_public_times_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Public, first);
            let b = BaseField::<Circuit>::new(Mode::Constant, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_private_times_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Private, first);
            let b = BaseField::<Circuit>::new(Mode::Constant, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_public_times_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Public, first);
            let b = BaseField::<Circuit>::new(Mode::Public, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 1, 1);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 1, 1);
        }
    }

    #[test]
    fn test_public_times_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Public, first);
            let b = BaseField::<Circuit>::new(Mode::Private, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 1, 1);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 1, 1);
        }
    }

    #[test]
    fn test_private_times_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Private, first);
            let b = BaseField::<Circuit>::new(Mode::Public, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 1, 1);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 1, 1);
        }
    }

    #[test]
    fn test_private_times_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());

            let expected = first * second;
            let a = BaseField::<Circuit>::new(Mode::Private, first);
            let b = BaseField::<Circuit>::new(Mode::Private, second);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 0, 0, 1, 1);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 0, 0, 1, 1);
        }
    }

    #[test]
    fn test_mul_matches() {
        // Sample two random elements.
        let a: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
        let b: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
        let expected = a * b;

        // Constant
        let first = BaseField::<Circuit>::new(Mode::Constant, a);
        let second = BaseField::<Circuit>::new(Mode::Constant, b);
        let candidate_a = first * second;
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let first = BaseField::<Circuit>::new(Mode::Private, a);
        let second = BaseField::<Circuit>::new(Mode::Private, b);
        let candidate_b = first * second;
        assert_eq!(expected, candidate_b.eject_value());
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
