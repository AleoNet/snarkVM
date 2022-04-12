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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

pub mod add;
pub mod double;
pub mod equal;
pub mod from_bits;
pub mod from_x_coordinate;
pub mod from_xy_coordinates;
pub mod mul;
pub mod neg;
pub mod sub;
pub mod ternary;
pub mod to_bits;
pub mod to_x_coordinate;
pub mod to_y_coordinate;
pub mod zero;

#[cfg(test)]
use snarkvm_circuits_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types_boolean::Boolean;
use snarkvm_circuits_types_field::Field;
use snarkvm_circuits_types_scalar::Scalar;
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};

#[derive(Clone)]
pub struct Group<E: Environment> {
    x: Field<E>,
    y: Field<E>,
}

impl<E: Environment> GroupTrait<Scalar<E>> for Group<E> {}

impl<E: Environment> Inject for Group<E> {
    type Primitive = E::Affine;

    ///
    /// Initializes a new affine group element.
    ///
    /// If only the x-coordinate is given, recovery of the y-coordinate is performed natively.
    ///
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    /// regardless of whether the y-coordinate was recovered.
    ///
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        // Initialize the x- and y-coordinate field elements.
        let x = Field::new(mode, value.to_x_coordinate());
        let y = Field::new(mode, value.to_y_coordinate());

        Self::from_xy_coordinates(x, y)
    }
}

impl<E: Environment> Eject for Group<E> {
    type Primitive = E::Affine;

    ///
    /// Ejects the mode of the group element.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.x, &self.y).eject_mode()
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

impl<E: Environment> Parser for Group<E> {
    type Environment = E;

    /// Parses a string into an affine group circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the x-coordinate from the string.
        let (string, x_coordinate): (&str, E::BaseField) =
            map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;
        // Recover and negate the group element if the negative sign was present.
        let group = match negation {
            true => -E::affine_from_x_coordinate(x_coordinate),
            false => E::affine_from_x_coordinate(x_coordinate),
        };
        match mode {
            Some((_, mode)) => Ok((string, Group::new(mode, group))),
            None => Ok((string, Group::new(Mode::Constant, group))),
        }
    }
}

impl<E: Environment> TypeName for Group<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        "group"
    }
}

impl<E: Environment> Debug for Group<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.x.eject_value(), self.y.eject_value())
    }
}

impl<E: Environment> Display for Group<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}.{}", self.x.eject_value(), Self::type_name(), self.eject_mode())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use core::str::FromStr;

    const ITERATIONS: usize = 128;

    /// Attempts to construct an affine group element from the given x-coordinate and mode.
    fn check_debug(mode: Mode, point: <Circuit as Environment>::Affine) {
        let x = point.to_x_coordinate();
        let y = point.to_y_coordinate();

        let candidate = Group::<Circuit>::new(mode, point);
        assert_eq!(format!("({}, {})", x, y), format!("{:?}", candidate));
    }

    #[test]
    fn test_new() {
        // Constant variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            Circuit::scope(&format!("Constant {}", i), || {
                let affine = Group::<Circuit>::new(Mode::Constant, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(4, 0, 0, 0);
            });
        }

        // Public variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            Circuit::scope(&format!("Public {}", i), || {
                let affine = Group::<Circuit>::new(Mode::Public, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(2, 2, 2, 3);
            });
        }

        // Private variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            Circuit::scope(&format!("Private {}", i), || {
                let affine = Group::<Circuit>::new(Mode::Private, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(2, 0, 4, 3);
            });
        }
    }

    #[test]
    fn test_debug() {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            // Constant
            check_debug(Mode::Constant, point);
            // Public
            check_debug(Mode::Public, point);
            // Private
            check_debug(Mode::Private, point);
        }
    }

    #[test]
    fn test_debug_zero() {
        let zero = <Circuit as Environment>::Affine::zero();

        // Constant
        let candidate = Group::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("(0, 1)", &format!("{:?}", candidate));

        // Public
        let candidate = Group::<Circuit>::new(Mode::Public, zero);
        assert_eq!("(0, 1)", &format!("{:?}", candidate));

        // Private
        let candidate = Group::<Circuit>::new(Mode::Private, zero);
        assert_eq!("(0, 1)", &format!("{:?}", candidate));
    }

    #[rustfmt::skip]
    #[test]
    fn test_parser() {
        type Primitive = <Circuit as Environment>::BaseField;

        // Constant

        let (_, candidate) = Group::<Circuit>::parse("2group").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("2_group").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("2group.constant").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("2_group.constant").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_constant());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group.constant", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_constant());

        // Public

        let (_, candidate) = Group::<Circuit>::parse("2group.public").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_public());

        let (_, candidate) = Group::<Circuit>::parse("2_group.public").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_public());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group.public", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_public());

        // Private

        let (_, candidate) = Group::<Circuit>::parse("2group.private").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_private());

        let (_, candidate) = Group::<Circuit>::parse("2_group.private").unwrap();
        assert_eq!(Primitive::from_str("2").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_private());

        let (_, candidate) = Group::<Circuit>::parse("6124_8679069_09631996143302_21072113214281104_6555821040_573308695_4291647607832_31_group.private", ).unwrap();
        assert_eq!(Primitive::from_str("6124867906909631996143302210721132142811046555821040573308695429164760783231").unwrap(), candidate.eject_value().to_x_coordinate());
        assert!(candidate.is_private());

        // Random

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for _ in 0..ITERATIONS {
                let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
                let expected = Group::<Circuit>::new(mode, point);

                let (_, candidate) = Group::<Circuit>::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }

    #[test]
    fn test_display() {
        let two = Circuit::affine_from_x_coordinate(<Circuit as Environment>::BaseField::one().double());

        // Constant
        let candidate = Group::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2group.constant", &format!("{}", candidate));

        // Public
        let candidate = Group::<Circuit>::new(Mode::Public, two);
        assert_eq!("2group.public", &format!("{}", candidate));

        // Private
        let candidate = Group::<Circuit>::new(Mode::Private, two);
        assert_eq!("2group.private", &format!("{}", candidate));
    }
}
