// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<E: Environment> Group<E> {
    /// Initializes an affine group element from a given x-coordinate field element.
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    pub fn from_x_coordinate(x: Field<E>) -> Self {
        // Derive the y-coordinate.
        let y = witness!(|x| match console::Group::from_x_coordinate(x) {
            Ok(point) => point.to_y_coordinate(),
            Err(_) => console::Field::zero(),
        });

        Self::from_xy_coordinates(x, y)
    }

    /// Initializes an affine group element from a given x-coordinate field element.
    /// Also returns an error flag, set if there is no group element with the given x-coordinate;
    /// in that case, the returned point is `(0, 0)`, but immaterial.
    pub fn from_x_coordinate_flagged(x: Field<E>) -> (Self, Boolean<E>) {
        // Obtain the A and D coefficients of the elliptic curve.
        let a = Field::constant(console::Field::new(E::EDWARDS_A));
        let d = Field::constant(console::Field::new(E::EDWARDS_D));

        // Compute x^2.
        let xx = &x * &x;

        // Compute a * x^2 - 1.
        let a_xx_minus_1 = a * &xx - Field::one();

        // Compute d * x^2 - 1.
        let d_xx_minus_1 = d * &xx - Field::one();

        // Compute y^2 = (a * x^2 - 1) / (d * x^2 - 1), i.e. solve the curve equation for y^2.
        let yy: Field<E> = witness!(|a_xx_minus_1, d_xx_minus_1| { a_xx_minus_1 / d_xx_minus_1 });
        E::enforce(|| (&yy, &d_xx_minus_1, &a_xx_minus_1));

        // Compute both square roots of y^2, in no specified order, with a flag saying whether y^2 is a square or not.
        // That is, finish solving the curve equation for y.
        // If the x-coordinate line does not intersect the elliptic curve, this returns (1, 0, 0).
        let (y1, y2, yy_is_not_square) = yy.square_roots_flagged_nondeterministic();

        // Form the two points, which are on the curve if yy_is_not_square is false.
        // Note that the Group<E> type is not restricted to the points in the subgroup or even on the curve;
        // it includes all possible points, i.e. all possible pairs of field elements.
        let point1 = Self { x: x.clone(), y: y1.clone() };
        let point2 = Self { x: x.clone(), y: y2.clone() };

        // We need to check whether either of the two points is in the subgroup.
        // There may be at most one, but in a circuit we need to always represent both computation paths.
        // In fact, we represent this computation also when yy_is_not_square is true,
        // in which case the results of checking whether either point is in the subgroup are meaningless,
        // but ignored in the final selection of the results returned below.
        // The criterion for membership in the subgroup is that
        // multiplying the point by the subgroup order yields the zero point (0, 1).
        // The group operation that we use here is for the type `Group<E>` of the subgroup,
        // which as mentioned above it can be performed on points outside the subgroup as well.
        // We turn the subgroup order into big endian bits,
        // to get around the issue that the subgroup order is not of Scalar<E> type.
        let order = E::ScalarField::modulus();
        let order_bits_be = order.to_bits_be();
        let mut order_bits_be_constants = Vec::with_capacity(order_bits_be.len());
        for bit in order_bits_be.iter() {
            order_bits_be_constants.push(Boolean::constant(*bit));
        }
        let point1_times_order = order_bits_be_constants.mul(point1);
        let point2_times_order = order_bits_be_constants.mul(point2);
        let point1_is_in_subgroup = point1_times_order.is_zero();
        let point2_is_in_subgroup = point2_times_order.is_zero();

        // We select y1 if (x, y1) is in the subgroup (which implies that (x, y2) is not in the subgroup),
        // or y2 if (x, y2) is in the subgroup (which implies that (x, y1) is not in the subgroup),
        // or 0 if neither is in the subgroup, or x does not even intersect the elliptic curve.
        // Since at most one of the two points can be in the subgroup, the order of y1 and y2 returned by square root is immaterial:
        // that nondeterminism (in the circuit) is resolved, and the circuit for from_x_coordinate_flagged is deterministic.
        let y2_or_zero = Field::ternary(&point2_is_in_subgroup, &y2, &Field::zero());
        let y1_or_y2_or_zero = Field::ternary(&point1_is_in_subgroup, &y1, &y2_or_zero);
        let y = Field::ternary(&yy_is_not_square, &Field::zero(), &y1_or_y2_or_zero);

        // The error flag is set iff x does not intersect the elliptic curve or neither intersection point is in the subgroup.
        let neither_in_subgroup = point1_is_in_subgroup.not().bitand(point2_is_in_subgroup.not());
        let error_flag = yy_is_not_square.bitor(&neither_in_subgroup);

        (Self { x, y }, error_flag)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_from_x_coordinate(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut rng);

            // Inject the x-coordinate.
            let x_coordinate = Field::new(mode, point.to_x_coordinate());

            Circuit::scope(format!("{mode} {i}"), || {
                let affine = Group::<Circuit>::from_x_coordinate(x_coordinate);
                assert_eq!(point, affine.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    fn check_from_x_coordinate_flagged(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random x coordinate.
            let x: console::Field<<Circuit as Environment>::Network> = Uniform::rand(&mut rng);
            // Compute error flag and point in console-land.
            let (expected_error_flag, expected_point) = match console::Group::from_x_coordinate(x) {
                Ok(point) => (false, point),
                Err(_) => (true, console::Group::from_xy_coordinates_unchecked(x, console::Field::zero())),
            };
            // Compute error flag and point in circuit-land.
            let input = Field::<Circuit>::new(mode, x);
            Circuit::scope(format!("{mode} {i}"), || {
                let (candidate_point, candidate_error_flag) = Group::from_x_coordinate_flagged(input);
                assert_eq!(expected_error_flag, candidate_error_flag.eject_value());
                assert_eq!(expected_point, candidate_point.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_from_x_coordinate_constant() {
        check_from_x_coordinate(Mode::Constant, 9, 0, 0, 0);
    }

    #[test]
    fn test_from_x_coordinate_public() {
        check_from_x_coordinate(Mode::Public, 4, 0, 13, 13);
    }

    #[test]
    fn test_from_x_coordinate_private() {
        check_from_x_coordinate(Mode::Private, 4, 0, 13, 13);
    }

    #[test]
    fn test_from_x_coordinate_flagged_constant() {
        check_from_x_coordinate_flagged(Mode::Constant, 3764, 0, 0, 0);
    }

    #[test]
    fn test_from_x_coordinate_flagged_public() {
        check_from_x_coordinate_flagged(Mode::Public, 1756, 0, 5861, 5861);
    }

    #[test]
    fn test_from_x_coordinate_flagged_private() {
        check_from_x_coordinate_flagged(Mode::Private, 1756, 0, 5861, 5861);
    }
}
