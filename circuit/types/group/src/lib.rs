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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
#![cfg_attr(test, allow(clippy::assertions_on_result_states))]

mod helpers;

pub mod add;
pub mod double;
pub mod equal;
pub mod mul;
pub mod neg;
pub mod sub;
pub mod ternary;

#[cfg(test)]
use console::{TestRng, Uniform};
#[cfg(test)]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use console::AffineCurve;
use snarkvm_circuit_environment::prelude::*;
use snarkvm_circuit_types_boolean::Boolean;
use snarkvm_circuit_types_field::Field;
use snarkvm_circuit_types_scalar::Scalar;

#[derive(Clone)]
pub struct Group<E: Environment> {
    x: Field<E>,
    y: Field<E>,
}

impl<E: Environment> GroupTrait<Scalar<E>> for Group<E> {}

impl<E: Environment> Group<E> {
    /// Returns the generator of the prime-order subgroup.
    pub fn generator() -> Self {
        Group::constant(console::Group::generator())
    }
}

#[cfg(console)]
impl<E: Environment> Inject for Group<E> {
    type Primitive = console::Group<E::Network>;

    /// Initializes a new affine group element.
    ///
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    /// regardless of whether the y-coordinate was recovered.
    fn new(mode: Mode, group: Self::Primitive) -> Self {
        // Allocate two new variables for the coordinates, with the mode and values given as inputs.
        let x = Field::new(mode, group.to_x_coordinate());
        let y = Field::new(mode, group.to_y_coordinate());
        // Put the coordinates together into a point.
        let point = Self { x, y };
        // Enforce in the circuit that the point is in the group.
        point.enforce_in_group();
        // Return the point.
        point
    }
}

impl<E: Environment> Group<E> {
    /// Enforces that `self` is on the curve.
    ///
    /// Ensure ax^2 + y^2 = 1 + dx^2y^2
    /// by checking that y^2 * (dx^2 - 1) = (ax^2 - 1)
    pub fn enforce_on_curve(&self) {
        let a = Field::constant(console::Field::new(E::EDWARDS_A));
        let d = Field::constant(console::Field::new(E::EDWARDS_D));

        let x2 = self.x.square();
        let y2 = self.y.square();

        let first = y2;
        let second = (d * &x2) - &Field::one();
        let third = (a * x2) - Field::one();

        // Ensure y^2 * (dx^2 - 1) = (ax^2 - 1).
        E::enforce(|| (first, second, third));
    }
}

impl<E: Environment> Group<E> {
    /// Enforces that `self` is on the curve and in the largest prime-order subgroup.
    pub fn enforce_in_group(&self) {
        let self_witness = self.eject_value();

        // Each point in the subgroup is the quadruple of some point on the curve,
        // where 'quadruple' refers to the cofactor 4 of the curve.
        // Thus, to enforce that a given point is in the group,
        // there must exist some point on the curve such that 4 times the latter yields the former.
        // The point on the curve is existentially quantified,
        // so the constraints introduce new coordinate variables for that point.

        // For the internal variables of this circuit,
        // the mode is constant if the input point is constant, otherwise private.
        let mode = if self.eject_mode().is_constant() { Mode::Constant } else { Mode::Private };

        // Postulate a point (two new R1CS variables) on the curve,
        // whose witness is the witness of the input point divided by the cofactor.
        let point_witness = self_witness.div_by_cofactor();
        let point_x = Field::new(mode, point_witness.to_x_coordinate());
        let point_y = Field::new(mode, point_witness.to_y_coordinate());
        let point = Self { x: point_x, y: point_y };
        point.enforce_on_curve();

        // (For advanced users) The cofactor for this curve is `4`. Thus doubling is used to be performant.
        debug_assert!(E::Affine::cofactor().len() == 1 && E::Affine::cofactor()[0] == 4);

        // Double the point on the curve.
        // This introduces two new R1CS variables for the doubled point.
        let double_point = point.double();

        // Enforce that the input point (self) is double the double of the point on the curve,
        // i.e. that it is 4 (= cofactor) times the postulated point on the curve.
        double_point.enforce_double(self);
    }
}

#[cfg(console)]
impl<E: Environment> Eject for Group<E> {
    type Primitive = console::Group<E::Network>;

    /// Ejects the mode of the group element.
    fn eject_mode(&self) -> Mode {
        (&self.x, &self.y).eject_mode()
    }

    /// Ejects the group as a constant group element.
    fn eject_value(&self) -> Self::Primitive {
        console::Group::from_xy_coordinates_unchecked(self.x.eject_value(), self.y.eject_value())
    }
}

#[cfg(console)]
impl<E: Environment> Parser for Group<E> {
    /// Parses a string into a group circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the group from the string.
        let (string, group) = console::Group::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Group::new(mode, group))),
            None => Ok((string, Group::new(Mode::Constant, group))),
        }
    }
}

#[cfg(console)]
impl<E: Environment> FromStr for Group<E> {
    type Err = Error;

    /// Parses a string into a group circuit.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

#[cfg(console)]
impl<E: Environment> TypeName for Group<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        console::Group::<E::Network>::type_name()
    }
}

#[cfg(console)]
impl<E: Environment> Debug for Group<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl<E: Environment> Display for Group<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}

impl<E: Environment> From<Group<E>> for LinearCombination<E::BaseField> {
    fn from(group: Group<E>) -> Self {
        From::from(&group)
    }
}

impl<E: Environment> From<&Group<E>> for LinearCombination<E::BaseField> {
    fn from(group: &Group<E>) -> Self {
        group.to_x_coordinate().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use core::str::FromStr;

    const ITERATIONS: u64 = 128;

    /// Attempts to construct an affine group element from the given x-coordinate and mode.
    fn check_display(mode: Mode, point: console::Group<<Circuit as Environment>::Network>) {
        let x = *point.to_x_coordinate();
        let candidate = Group::<Circuit>::new(mode, point);
        assert_eq!(format!("{x}{}.{mode}", Group::<Circuit>::type_name()), format!("{candidate}"));
    }

    #[test]
    fn test_new() {
        let mut rng = TestRng::default();

        // Constant variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut rng);

            Circuit::scope(&format!("Constant {i}"), || {
                let affine = Group::<Circuit>::new(Mode::Constant, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(10, 0, 0, 0);
            });
        }

        // Public variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut rng);

            Circuit::scope(&format!("Public {i}"), || {
                let affine = Group::<Circuit>::new(Mode::Public, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(4, 2, 12, 13);
            });
        }

        // Private variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut rng);

            Circuit::scope(&format!("Private {i}"), || {
                let affine = Group::<Circuit>::new(Mode::Private, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(4, 0, 14, 13);
            });
        }
    }

    #[test]
    fn test_display() {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut rng);

            // Constant
            check_display(Mode::Constant, point);
            // Public
            check_display(Mode::Public, point);
            // Private
            check_display(Mode::Private, point);
        }
    }

    #[test]
    fn test_display_zero() {
        let zero = console::Group::<<Circuit as Environment>::Network>::zero();

        // Constant
        let candidate = Group::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("0group.constant", &format!("{candidate}"));

        // Public
        let candidate = Group::<Circuit>::new(Mode::Public, zero);
        assert_eq!("0group.public", &format!("{candidate}"));

        // Private
        let candidate = Group::<Circuit>::new(Mode::Private, zero);
        assert_eq!("0group.private", &format!("{candidate}"));
    }

    #[rustfmt::skip]
    #[test]
    fn test_parser() {
        type Primitive = console::Group<<Circuit as Environment>::Network>;

        // Constant

        let (_, candidate) = Group::<Circuit>::parse("2group").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("2_group").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231group").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("2group.constant").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("2_group.constant").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group.constant", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231group").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        // Public

        let (_, candidate) = Group::<Circuit>::parse("2group.public").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Group::<Circuit>::parse("2_group.public").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group.public", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231group").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        // Private

        let (_, candidate) = Group::<Circuit>::parse("2group.private").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Group::<Circuit>::parse("2_group.private").unwrap();
        assert_eq!(Primitive::from_str("2group").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group.private", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231group").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        // Random

        let mut rng = TestRng::default();

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for _ in 0..ITERATIONS {
                let point = Uniform::rand(&mut rng);
                let expected = Group::<Circuit>::new(mode, point);

                let (_, candidate) = Group::<Circuit>::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }
}
