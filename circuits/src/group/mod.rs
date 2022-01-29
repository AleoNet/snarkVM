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
pub mod mul;
pub mod neg;
// pub mod one;
pub mod sub;
pub mod ternary;
pub mod zero;

use crate::{traits::*, BaseField, Boolean, Environment, Mode, ScalarField};
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field as F, One as O};

#[cfg(test)]
use snarkvm_fields::Zero as Z;

use std::{
    fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Clone)]
pub struct Affine<E: Environment> {
    x: BaseField<E>,
    y: BaseField<E>,
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
            None => E::affine_from_x_coordinate(x).to_y_coordinate(),
        };

        // Initialize the x- and y-coordinate field elements.
        let x = BaseField::new(mode, x);
        let y = BaseField::new(mode, y);

        Self::from(x, y)
    }

    ///
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    /// regardless of whether the y-coordinate was recovered.
    ///
    pub fn from(x: BaseField<E>, y: BaseField<E>) -> Self {
        //
        // Check the point is on the curve.
        //
        // Ensure ax^2 + y^2 = 1 + dx^2y^2
        // by checking that y^2 * (dx^2 - 1) = (ax^2 - 1)
        //
        {
            let a = BaseField::new(Mode::Constant, E::AffineParameters::COEFF_A);
            let d = BaseField::new(Mode::Constant, E::AffineParameters::COEFF_D);

            let x2 = x.square();
            let y2 = y.square();

            let first = y2;
            let second = (d * &x2) - &BaseField::one();
            let third = (a * x2) - BaseField::one();

            // Ensure y^2 * (dx^2 - 1) = (ax^2 - 1).
            E::enforce(|| (first, second, third));
        }

        Self { x, y }
    }
}

impl<E: Environment> Eject for Affine<E> {
    type Primitive = E::Affine;

    ///
    /// Ejects the mode of the group element.
    ///
    fn eject_mode(&self) -> Mode {
        match (self.x.eject_mode(), self.y.eject_mode()) {
            (Mode::Constant, mode) | (mode, Mode::Constant) => mode,
            (Mode::Public, Mode::Public) => Mode::Public,
            (Mode::Private, mode) | (mode, Mode::Private) => mode,
        }
    }

    ///
    /// Ejects the group as a constant group element.
    ///
    fn eject_value(&self) -> E::Affine {
        let value = E::affine_from_x_coordinate(self.x.eject_value());
        assert_eq!(value.to_y_coordinate(), self.y.eject_value());
        value
    }
}

impl<E: Environment> fmt::Debug for Affine<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.x.eject_value(), self.y.eject_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 250;

    /// Attempts to construct an affine group element from the given x-coordinate and mode.
    fn check_debug(mode: Mode, x: <Circuit as Environment>::BaseField, y: <Circuit as Environment>::BaseField) {
        let candidate = Affine::<Circuit>::new(mode, x, None);
        assert_eq!(format!("({}, {})", x, y), format!("{:?}", candidate));
    }

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
                let recovered = Circuit::affine_from_x_coordinate(x_coordinate);
                assert_eq!(x_coordinate, recovered.to_x_coordinate());
                assert_eq!(y_coordinate, recovered.to_y_coordinate());
            }

            Circuit::scoped(&format!("Constant {}", i), || {
                let affine = Affine::<Circuit>::new(Mode::Constant, x_coordinate, None);
                assert_eq!(point, affine.eject_value());

                assert_eq!(4, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());
            });
        }

        // Public variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let x_coordinate = point.to_x_coordinate();

            Circuit::scoped(&format!("Public {}", i), || {
                let affine = Affine::<Circuit>::new(Mode::Public, x_coordinate, None);
                assert_eq!(point, affine.eject_value());

                assert_eq!(2, Circuit::num_constants_in_scope());
                assert_eq!(2, Circuit::num_public_in_scope());
                assert_eq!(2, Circuit::num_private_in_scope());
                assert_eq!(3, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());
            });
        }

        // Private variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let x_coordinate = point.to_x_coordinate();

            Circuit::scoped(&format!("Private {}", i), || {
                let affine = Affine::<Circuit>::new(Mode::Private, x_coordinate, None);
                assert_eq!(point, affine.eject_value());

                assert_eq!(2, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(4, Circuit::num_private_in_scope());
                assert_eq!(3, Circuit::num_constraints_in_scope());
                assert!(Circuit::is_satisfied());
            });
        }
    }

    #[test]
    fn test_debug() {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let x_coordinate = point.to_x_coordinate();
            let y_coordinate = point.to_y_coordinate();

            // Constant
            check_debug(Mode::Constant, x_coordinate, y_coordinate);
            // Public
            check_debug(Mode::Public, x_coordinate, y_coordinate);
            // Private
            check_debug(Mode::Private, x_coordinate, y_coordinate);
        }
    }

    #[test]
    fn test_debug_zero() {
        let zero = <Circuit as Environment>::BaseField::zero();

        // Constant
        let candidate = Affine::<Circuit>::new(Mode::Constant, zero, None);
        assert_eq!("(0, 1)", &format!("{:?}", candidate));

        // Public
        let candidate = Affine::<Circuit>::new(Mode::Public, zero, None);
        assert_eq!("(0, 1)", &format!("{:?}", candidate));

        // Private
        let candidate = Affine::<Circuit>::new(Mode::Private, zero, None);
        assert_eq!("(0, 1)", &format!("{:?}", candidate));
    }
}
