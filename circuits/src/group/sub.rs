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

impl<E: Environment> Sub<Self> for Affine<E> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment> Sub<&Self> for Affine<E> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        self + -other
    }
}

impl<E: Environment> Sub<&Affine<E>> for &Affine<E> {
    type Output = Affine<E>;

    fn sub(self, other: &Affine<E>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment> SubAssign<Self> for Affine<E> {
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<E: Environment> SubAssign<&Self> for Affine<E> {
    fn sub_assign(&mut self, other: &Self) {
        *self = self.clone() + -other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_sub(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Affine<Circuit>,
        b: &Affine<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = a - b;
            assert_eq!(*expected, candidate.eject_value(), "({} - {})", a.eject_value(), b.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    fn check_sub_assign(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Affine<Circuit>,
        b: &Affine<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let mut candidate = a.clone();
            candidate -= b;
            assert_eq!(*expected, candidate.eject_value(), "({} - {})", a.eject_value(), b.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_constant_minus_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Constant, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Constant, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 4, 0, 0, 0);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 4, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_minus_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Constant, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Public, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_minus_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Public, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Constant, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_constant_minus_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Constant, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Private, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_private_minus_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Private, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Constant, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_minus_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Public, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Public, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_public_minus_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Public, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Private, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_minus_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Private, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Public, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_minus_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first - second;
            let a = Affine::<Circuit>::new(Mode::Private, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Private, second.to_x_coordinate(), None);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_sub_matches() {
        // Sample two random elements.
        let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
        let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
        let expected = a - b;

        // Constant
        let first = Affine::<Circuit>::new(Mode::Constant, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let second = Affine::<Circuit>::new(Mode::Constant, b.to_x_coordinate(), Some(b.to_y_coordinate()));
        let candidate_a = first - second;
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let first = Affine::<Circuit>::new(Mode::Private, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let second = Affine::<Circuit>::new(Mode::Private, b.to_x_coordinate(), Some(b.to_y_coordinate()));
        let candidate_b = first - second;
        assert_eq!(expected, candidate_b.eject_value());
    }
}
