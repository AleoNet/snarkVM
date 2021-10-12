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

pub mod add;
pub mod double;
pub mod equal;
// pub mod inv;
pub mod mul;
pub mod neg;
// pub mod one;
// pub mod sub;
pub mod zero;

use crate::{boolean::Boolean, traits::*, Environment, Field, Mode};
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field as F, One as O, Zero as Z};

// use num_traits::Inv;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[derive(Clone)]
pub struct Affine<E: Environment> {
    x: Field<E>,
    y: Field<E>,
}

impl<E: Environment> Affine<E> {
    ///
    /// Initializes a new affine group element.
    ///
    /// If only the x-coordinate is given, recovery of the y-coordinate is performed natively.
    ///
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    /// regardless of whether the y-coordinate was recovered.
    ///
    pub fn new(mode: Mode, x: E::BaseField, y: Option<E::BaseField>) -> Self {
        // Derive the y-coordinate if it is not given.
        let y = match y {
            Some(y) => y,
            None => E::recover_from_x_coordinate(x).to_y_coordinate(),
        };

        // Initialize the x- and y-coordinate field elements.
        let x = Field::new(mode, x);
        let y = Field::new(mode, y);

        Self::from(x, y)
    }

    ///
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    /// regardless of whether the y-coordinate was recovered.
    ///
    pub fn from(x: Field<E>, y: Field<E>) -> Self {
        //
        // Check the point is on the curve.
        //
        // Ensure ax^2 + y^2 = 1 + dx^2y^2
        // by checking that y^2 * (dx^2 - 1) = (ax^2 - 1)
        //
        {
            let a = Field::new(Mode::Constant, E::AffineParameters::COEFF_A);
            let d = Field::new(Mode::Constant, E::AffineParameters::COEFF_D);

            let x2 = x.square();
            let y2 = y.square();

            let first = y2;
            let second = (d * &x2) - &Field::one();
            let third = (a * x2) - Field::one();

            // Ensure y^2 * (dx^2 - 1) = (ax^2 - 1).
            E::enforce(|| (first, second, third));
        }

        Self { x, y }
    }

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() && self.y.is_constant()
    }

    pub fn to_value(&self) -> (E::BaseField, E::BaseField) {
        (self.x.to_value(), self.y.to_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 500;

    #[test]
    fn test_new() {
        // Constant variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let x_coordinate = point.to_x_coordinate();
            let y_coordinate = point.to_y_coordinate();
            {
                // Verify the recovery method is behaving correctly.
                let recovered = Circuit::recover_from_x_coordinate(x_coordinate);
                assert_eq!(x_coordinate, recovered.to_x_coordinate());
                assert_eq!(y_coordinate, recovered.to_y_coordinate());
            }

            Circuit::scoped(&format!("Constant {}", i), |scope| {
                let affine = Affine::<Circuit>::new(Mode::Constant, x_coordinate, None);
                assert_eq!((x_coordinate, y_coordinate), affine.to_value());

                assert_eq!(8, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });
        }

        // Public variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let x_coordinate = point.to_x_coordinate();
            let y_coordinate = point.to_y_coordinate();

            Circuit::scoped(&format!("Public {}", i), |scope| {
                let affine = Affine::<Circuit>::new(Mode::Public, x_coordinate, None);
                assert_eq!((x_coordinate, y_coordinate), affine.to_value());

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(2, scope.num_public_in_scope());
                assert_eq!(2, scope.num_private_in_scope());
                assert_eq!(3, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }

        // Private variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let x_coordinate = point.to_x_coordinate();
            let y_coordinate = point.to_y_coordinate();

            Circuit::scoped(&format!("Private {}", i), |scope| {
                let affine = Affine::<Circuit>::new(Mode::Private, x_coordinate, None);
                assert_eq!((x_coordinate, y_coordinate), affine.to_value());

                assert_eq!(2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(4, scope.num_private_in_scope());
                assert_eq!(3, scope.num_constraints_in_scope());
                assert!(scope.is_satisfied());
            });
        }
    }
}
