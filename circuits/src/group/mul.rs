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

impl<E: Environment> Mul<ScalarField<E>> for Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: ScalarField<E>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<ScalarField<E>> for &Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: ScalarField<E>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment> Mul<&ScalarField<E>> for Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: &ScalarField<E>) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&ScalarField<E>> for &Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: &ScalarField<E>) -> Self::Output {
        (*self).clone() * other
    }
}

impl<E: Environment> Mul<Affine<E>> for ScalarField<E> {
    type Output = Affine<E>;

    fn mul(self, other: Affine<E>) -> Self::Output {
        other * &self
    }
}

impl<E: Environment> Mul<Affine<E>> for &ScalarField<E> {
    type Output = Affine<E>;

    fn mul(self, other: Affine<E>) -> Self::Output {
        &other * self
    }
}

impl<E: Environment> Mul<&Affine<E>> for ScalarField<E> {
    type Output = Affine<E>;

    fn mul(self, other: &Affine<E>) -> Self::Output {
        other * &self
    }
}

impl<E: Environment> Mul<&Affine<E>> for &ScalarField<E> {
    type Output = Affine<E>;

    fn mul(self, other: &Affine<E>) -> Self::Output {
        other * self
    }
}

impl<E: Environment> MulAssign<ScalarField<E>> for Affine<E> {
    fn mul_assign(&mut self, other: ScalarField<E>) {
        *self *= &other;
    }
}

impl<E: Environment> MulAssign<&ScalarField<E>> for Affine<E> {
    fn mul_assign(&mut self, other: &ScalarField<E>) {
        *self *= other.to_bits_be().as_slice();
    }
}

impl<E: Environment, const N: usize> Mul<[Boolean<E>; N]> for Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: [Boolean<E>; N]) -> Self::Output {
        self * &other[..]
    }
}

impl<E: Environment, const N: usize> Mul<[Boolean<E>; N]> for &Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: [Boolean<E>; N]) -> Self::Output {
        self * &other[..]
    }
}

impl<E: Environment> Mul<&[Boolean<E>]> for Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: &[Boolean<E>]) -> Self::Output {
        let mut output = self;
        output *= other;
        output
    }
}

impl<E: Environment> Mul<&[Boolean<E>]> for &Affine<E> {
    type Output = Affine<E>;

    fn mul(self, other: &[Boolean<E>]) -> Self::Output {
        (*self).clone() * other
    }
}

impl<E: Environment, const N: usize> Mul<Affine<E>> for [Boolean<E>; N] {
    type Output = Affine<E>;

    fn mul(self, other: Affine<E>) -> Self::Output {
        other * &self[..]
    }
}

impl<E: Environment> Mul<Affine<E>> for &[Boolean<E>] {
    type Output = Affine<E>;

    fn mul(self, other: Affine<E>) -> Self::Output {
        &other * self
    }
}

impl<E: Environment, const N: usize> Mul<&Affine<E>> for [Boolean<E>; N] {
    type Output = Affine<E>;

    fn mul(self, other: &Affine<E>) -> Self::Output {
        other * &self[..]
    }
}

impl<E: Environment> Mul<&Affine<E>> for &[Boolean<E>] {
    type Output = Affine<E>;

    fn mul(self, other: &Affine<E>) -> Self::Output {
        other * self
    }
}

impl<E: Environment, const N: usize> MulAssign<[Boolean<E>; N]> for Affine<E> {
    fn mul_assign(&mut self, other: [Boolean<E>; N]) {
        *self *= &other[..];
    }
}

impl<E: Environment> MulAssign<&[Boolean<E>]> for Affine<E> {
    fn mul_assign(&mut self, other: &[Boolean<E>]) {
        let base = self.clone();

        let mut output = Affine::zero();
        for bit in other.iter() {
            output = output.double();
            output = Ternary::ternary(bit, &(&base + &output), &output);
        }
        *self = output;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 10;

    fn check_mul(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Affine<Circuit>,
        b: &ScalarField<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a * b;
            assert_eq!(
                *expected,
                candidate.eject_value(),
                "{} != {} := ({} * {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    fn check_mul_assign(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Affine<Circuit>,
        b: &ScalarField<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let mut candidate = a.clone();
            candidate *= b;
            assert_eq!(
                *expected,
                candidate.eject_value(),
                "{} != {} := ({} * {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_constant_times_scalar_constant() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Constant, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Constant, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 1757, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 1757, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_times_scalar_public() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Constant, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Public, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 757, 0, 2500, 2500);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 757, 0, 2500, 2500);
        }
    }

    #[test]
    fn test_constant_times_scalar_private() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Constant, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Private, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 757, 0, 2500, 2500);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 757, 0, 2500, 2500);
        }
    }

    #[test]
    fn test_public_times_scalar_constant() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Public, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Constant, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 759, 0, 2737, 2745);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 759, 0, 2737, 2745);
        }
    }

    #[test]
    fn test_private_times_scalar_constant() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Private, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Constant, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 759, 0, 2737, 2745);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 759, 0, 2737, 2745);
        }
    }

    #[test]
    fn test_public_times_scalar_public() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Public, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Public, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_public_times_scalar_private() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Public, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Private, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_private_times_scalar_public() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Private, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Public, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_private_times_scalar_private() {
        for i in 0..ITERATIONS {
            let base: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let scalar: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            let expected = base * scalar;
            let a = Affine::<Circuit>::new(Mode::Private, base.to_x_coordinate(), None);
            let b = ScalarField::<Circuit>::new(Mode::Private, scalar);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, &expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, &expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_mul_matches() {
        // Sample two random elements.
        let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
        let b: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());
        let expected = a * b;

        // Constant
        let base = Affine::<Circuit>::new(Mode::Constant, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let scalar = ScalarField::<Circuit>::new(Mode::Constant, b);
        let candidate_a = base * scalar;
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let base = Affine::<Circuit>::new(Mode::Private, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let scalar = ScalarField::<Circuit>::new(Mode::Private, b);
        let candidate_b = base * scalar;
        assert_eq!(expected, candidate_b.eject_value());
    }
}
