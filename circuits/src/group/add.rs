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

impl<E: Environment> Add<Self> for Affine<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment> Add<&Self> for Affine<E> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // This swap reduces the number of constants by one.
        let (this, that) = match other.is_constant() {
            true => (&self, other),
            false => (other, &self),
        };

        let a = BaseField::new(Mode::Constant, E::AffineParameters::COEFF_A);
        let d = BaseField::new(Mode::Constant, E::AffineParameters::COEFF_D);

        // Compute U = (-A * x1 + y1) * (x2 + y2)
        let u1 = (&this.x * &-&a) + &this.y;
        let u2 = &that.x + &that.y;
        let u = u1 * u2;

        // Compute v0 = x1 * y2
        let v0 = &this.x * &that.y;

        // Compute v1 = x2 * y1
        let v1 = &that.x * &this.y;

        // Compute v2 = d * v0 * v1
        let v2 = (&v0 * &v1) * d;

        // Compute x3 and y3.
        let (x3, y3) = {
            let v0 = v0.eject_value();
            let v1 = v1.eject_value();
            let v2 = v2.eject_value();

            // Assign x3 = (v0 + v1) / (v2 + 1)
            let x3 = {
                let t0 = v0 + v1;
                let t1 = v2 + E::BaseField::one();
                let t0_div_t1 = t0 * t1.inverse().expect("Failed to compute x-coordinate");
                BaseField::new(mode, t0_div_t1)
            };

            // Assign y3 = (U + a * v0 - v1) / (1 - v2)
            let y3 = {
                let t0 = u.eject_value() + (v0 * a.eject_value()) - v1;
                let t1 = E::BaseField::one() - v2;
                let t0_div_t1 = t0 * t1.inverse().expect("Failed to compute y-coordinate");
                BaseField::new(mode, t0_div_t1)
            };

            (x3, y3)
        };

        // Ensure x3 is well-formed.
        // x3 * (v2 + 1) = v0 + v1
        let v2_plus_one = &v2 + &BaseField::one();
        let v0_plus_v1 = &v0 + &v1;
        E::enforce(|| (&x3, v2_plus_one, v0_plus_v1));

        // Ensure y3 is well-formed.
        // y3 * (1 - v2) = u + (a * v0) - v1
        let one_minus_v2 = BaseField::one() - v2;
        let a_v0 = v0 * a;
        let u_plus_a_v0_minus_v1 = u + a_v0 - v1;
        E::enforce(|| (&y3, one_minus_v2, u_plus_a_v0_minus_v1));

        Self { x: x3, y: y3 }
    }
}

impl<E: Environment> Add<&Affine<E>> for &Affine<E> {
    type Output = Affine<E>;

    fn add(self, other: &Affine<E>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment> AddAssign<Self> for Affine<E> {
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<E: Environment> AddAssign<&Self> for Affine<E> {
    fn add_assign(&mut self, other: &Self) {
        *self = self.clone() + other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_add(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Affine<Circuit>,
        b: &Affine<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a + b;
            assert_eq!(
                *expected,
                candidate.eject_value(),
                "{} != {} := ({} + {})",
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

    fn check_add_assign(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Affine<Circuit>,
        b: &Affine<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let mut candidate = a.clone();
            candidate += b;
            assert_eq!(
                *expected,
                candidate.eject_value(),
                "{} != {} := ({} + {})",
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
    fn test_constant_plus_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Constant, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Constant, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 4, 0, 0, 0);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 4, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_plus_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Constant, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Public, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_plus_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Public, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Constant, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_constant_plus_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Constant, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Private, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_private_plus_constant() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Private, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Constant, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_plus_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Public, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Public, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_public_plus_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Public, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Private, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_plus_public() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Private, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Public, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_plus_private() {
        for i in 0..ITERATIONS {
            let first: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let second: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());

            let expected = first + second;
            let a = Affine::<Circuit>::new(Mode::Private, first.to_x_coordinate(), None);
            let b = Affine::<Circuit>::new(Mode::Private, second.to_x_coordinate(), None);

            let name = format!("Add: a + b {}", i);
            check_add(&name, &expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, &expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_add_matches() {
        // Sample two random elements.
        let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
        let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
        let expected = a + b;

        // Constant
        let first = Affine::<Circuit>::new(Mode::Constant, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let second = Affine::<Circuit>::new(Mode::Constant, b.to_x_coordinate(), Some(b.to_y_coordinate()));
        let candidate_a = first + second;
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let first = Affine::<Circuit>::new(Mode::Private, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let second = Affine::<Circuit>::new(Mode::Private, b.to_x_coordinate(), Some(b.to_y_coordinate()));
        let candidate_b = first + second;
        assert_eq!(expected, candidate_b.eject_value());
    }
}
