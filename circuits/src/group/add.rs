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

impl<E: Environment> Add<Self> for Affine<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment> Add<&Self> for Affine<E> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        if self.is_constant() && other.is_constant() {
            let (x1, y1) = self.to_value();
            let (x2, y2) = other.to_value();

            let y1y2 = y1 * y2;
            let x1x2 = x1 * x2;

            let ax1x2 = E::AffineParameters::COEFF_A * x1x2;
            let dx1x2y1y2 = E::AffineParameters::COEFF_D * y1y2 * x1x2;

            let d1 = E::BaseField::one() + dx1x2y1y2;
            let d2 = E::BaseField::one() - dx1x2y1y2;

            let x1y2 = x1 * y2;
            let y1x2 = y1 * x2;

            let x = (x1y2 + y1x2) / &d1;
            let y = (y1y2 - ax1x2) / &d2;

            return Self::new(Mode::Constant, x, Some(y));
        }

        let a = Field::new(Mode::Constant, E::AffineParameters::COEFF_A);
        let d = Field::new(Mode::Constant, E::AffineParameters::COEFF_D);

        // Compute U = (-A * x1 + y1) * (x2 + y2)
        let u1 = (&self.x * &-&a) + &self.y;
        let u2 = &other.x + &other.y;
        let u = u1 * u2;

        // Compute v0 = x1 * y2
        let v0 = &self.x * &other.y;

        // Compute v1 = x2 * y1
        let v1 = &other.x * &self.y;

        // Compute v2 = d * v0 * v1
        let v2 = (&v0 * &v1) * d;

        // Compute x3 and y3.
        let (x3, y3) = {
            let v0 = v0.to_value();
            let v1 = v1.to_value();
            let v2 = v2.to_value();

            // Assign x3 = (v0 + v1) / (v2 + 1)
            let x3 = {
                let t0 = v0 + v1;
                let t1 = v2 + E::BaseField::one();
                let t0_div_t1 = t0 * t1.inverse().expect("Failed to compute x-coordinate");
                Field::new(Mode::Private, t0_div_t1)
            };

            // Assign y3 = (U + a * v0 - v1) / (1 - v2)
            let y3 = {
                let t0 = u.to_value() + (v0 * a.to_value()) - v1;
                let t1 = E::BaseField::one() - v2;
                let t0_div_t1 = t0 * t1.inverse().expect("Failed to compute y-coordinate");
                Field::new(Mode::Private, t0_div_t1)
            };

            (x3, y3)
        };

        // Ensure x3 is well-formed.
        // x3 * (v2 + 1) = v0 + v1
        let v2_plus_one = &v2 + &Field::one();
        let v0_plus_v1 = &v0 + &v1;
        E::enforce(|| (&x3, v2_plus_one, v0_plus_v1));

        // Ensure y3 is well-formed.
        // y3 * (1 - v2) = u + (a * v0) - v1
        let one_minus_v2 = Field::one() - v2;
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

    #[test]
    fn test_add() {
        // Constant + Constant
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = a + b;

            let a = Affine::<Circuit>::new(Mode::Constant, a.to_x_coordinate(), Some(a.to_y_coordinate()));
            let b = Affine::<Circuit>::new(Mode::Constant, b.to_x_coordinate(), Some(b.to_y_coordinate()));

            Circuit::scoped(&format!("Constant + Constant {}", i), |scope| {
                let candidate = a + b;
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(8, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });
        }

        // Constant + Public
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = a + b;

            let a = Affine::<Circuit>::new(Mode::Constant, a.to_x_coordinate(), Some(a.to_y_coordinate()));
            let b = Affine::<Circuit>::new(Mode::Public, b.to_x_coordinate(), Some(b.to_y_coordinate()));

            Circuit::scoped(&format!("Constant + Public {}", i), |scope| {
                let candidate = a + b;
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(3, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(3, scope.num_private_in_scope());
                assert_eq!(3, scope.num_constraints_in_scope());
            });
        }

        // Public + Constant
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = a + b;

            let a = Affine::<Circuit>::new(Mode::Public, a.to_x_coordinate(), Some(a.to_y_coordinate()));
            let b = Affine::<Circuit>::new(Mode::Constant, b.to_x_coordinate(), Some(b.to_y_coordinate()));

            Circuit::scoped(&format!("Public + Constant {}", i), |scope| {
                let candidate = a + b;
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(3, scope.num_private_in_scope());
                assert_eq!(3, scope.num_constraints_in_scope());
            });
        }

        // Public + Public
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = a + b;

            let a = Affine::<Circuit>::new(Mode::Public, a.to_x_coordinate(), Some(a.to_y_coordinate()));
            let b = Affine::<Circuit>::new(Mode::Public, b.to_x_coordinate(), Some(b.to_y_coordinate()));

            Circuit::scoped(&format!("Public + Public {}", i), |scope| {
                let candidate = a + b;
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(6, scope.num_private_in_scope());
                assert_eq!(6, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Public + Private
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = a + b;

            let a = Affine::<Circuit>::new(Mode::Public, a.to_x_coordinate(), Some(a.to_y_coordinate()));
            let b = Affine::<Circuit>::new(Mode::Private, b.to_x_coordinate(), Some(b.to_y_coordinate()));

            Circuit::scoped(&format!("Public + Private {}", i), |scope| {
                let candidate = a + b;
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(6, scope.num_private_in_scope());
                assert_eq!(6, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Private + Private
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = a + b;

            let a = Affine::<Circuit>::new(Mode::Private, a.to_x_coordinate(), Some(a.to_y_coordinate()));
            let b = Affine::<Circuit>::new(Mode::Private, b.to_x_coordinate(), Some(b.to_y_coordinate()));

            Circuit::scoped(&format!("Private + Private {}", i), |scope| {
                let candidate = a + b;
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(6, scope.num_private_in_scope());
                assert_eq!(6, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
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
        assert_eq!(
            (expected.to_x_coordinate(), expected.to_y_coordinate()),
            candidate_a.to_value()
        );

        // Private
        let first = Affine::<Circuit>::new(Mode::Private, a.to_x_coordinate(), Some(a.to_y_coordinate()));
        let second = Affine::<Circuit>::new(Mode::Private, b.to_x_coordinate(), Some(b.to_y_coordinate()));
        let candidate_b = first + second;
        assert_eq!(
            (expected.to_x_coordinate(), expected.to_y_coordinate()),
            candidate_b.to_value()
        );
    }
}
