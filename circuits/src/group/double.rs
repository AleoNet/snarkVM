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

impl<E: Environment> Double for Affine<E> {
    type Output = Affine<E>;

    fn double(self) -> Self::Output {
        (&self).double()
    }
}

impl<E: Environment> Double for &Affine<E> {
    type Output = Affine<E>;

    fn double(self) -> Self::Output {
        if self.is_constant() {
            return self.clone() + self;
        }

        let a = Field::new(Mode::Constant, E::AffineParameters::COEFF_A);
        let two = Field::new(Mode::Constant, E::BaseField::one()).double();

        // Compute xy, xx, yy, axx.
        let xy = &self.x * &self.y;
        let x2 = self.x.square();
        let y2 = self.y.square();
        let ax2 = &x2 * &a;

        // Compute x3 and y3.
        let (x3, y3) = {
            let xy = xy.to_value();
            let x2 = x2.to_value();
            let y2 = y2.to_value();
            let ax2 = ax2.to_value();
            let two = E::BaseField::one() + E::BaseField::one();

            // Assign x3 = (2xy) / (ax^2 + y^2)
            let x3 = {
                let t0 = xy.double();
                let t1 = (E::AffineParameters::COEFF_A * x2) + y2;
                let t0_div_t1 = t0 * t1.inverse().expect("Failed to compute x-coordinate");
                Field::new(Mode::Private, t0_div_t1)
            };

            // Assign y3 = (y^2 - ax^2) / (2 - ax^2 - y^2)
            let y3 = {
                let t0 = y2 - ax2;
                let t1 = two - ax2 - y2;
                let t0_div_t1 = t0 * t1.inverse().expect("Failed to compute y-coordinate");
                Field::new(Mode::Private, t0_div_t1)
            };

            (x3, y3)
        };

        // Ensure x3 is well-formed.
        // x3 * (ax^2 + y^2) = 2xy
        let ax2_plus_y2 = &ax2 + &y2;
        let two_xy = xy.double();
        E::enforce(|| (&x3, &ax2_plus_y2, two_xy));

        // Ensure y3 is well-formed.
        // y3 * (2 - (ax^2 + y^2)) = y^2 - ax^2
        let y2_minus_a_x2 = y2 - ax2;
        let two_minus_ax2_minus_y2 = two - ax2_plus_y2;
        E::enforce(|| (&y3, two_minus_ax2_minus_y2, y2_minus_a_x2));

        Affine { x: x3, y: y3 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_curves::Group;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 500;

    #[test]
    fn test_double() {
        // Constant variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = point.double();

            let affine = Affine::<Circuit>::new(Mode::Constant, point.to_x_coordinate(), Some(point.to_y_coordinate()));

            Circuit::scoped(&format!("Constant {}", i), |scope| {
                let candidate = affine.double();
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(9, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });
        }

        // Public variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = point.double();

            let affine = Affine::<Circuit>::new(Mode::Public, point.to_x_coordinate(), Some(point.to_y_coordinate()));

            Circuit::scoped(&format!("Public {}", i), |scope| {
                let candidate = affine.double();
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(5, scope.num_private_in_scope());
                assert_eq!(5, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Private variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = point.double();

            let affine = Affine::<Circuit>::new(Mode::Private, point.to_x_coordinate(), Some(point.to_y_coordinate()));

            Circuit::scoped(&format!("Private {}", i), |scope| {
                let candidate = affine.double();
                assert_eq!(
                    (expected.to_x_coordinate(), expected.to_y_coordinate()),
                    candidate.to_value()
                );

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(5, scope.num_private_in_scope());
                assert_eq!(5, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }
    }

    #[test]
    fn test_double_matches() {
        // Sample two random elements.
        let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
        let expected = a + a;

        // Constant
        let candidate_a =
            Affine::<Circuit>::new(Mode::Constant, a.to_x_coordinate(), Some(a.to_y_coordinate())).double();
        assert_eq!(
            (expected.to_x_coordinate(), expected.to_y_coordinate()),
            candidate_a.to_value()
        );

        // Private
        let candidate_b =
            Affine::<Circuit>::new(Mode::Private, a.to_x_coordinate(), Some(a.to_y_coordinate())).double();
        assert_eq!(
            (expected.to_x_coordinate(), expected.to_y_coordinate()),
            candidate_b.to_value()
        );
    }
}
