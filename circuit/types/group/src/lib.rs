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

mod helpers;

pub mod add;
pub mod double;
pub mod equal;
pub mod mul;
pub mod neg;
pub mod sub;
pub mod ternary;

#[cfg(test)]
use console::{test_rng, Uniform};
#[cfg(test)]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use console::AffineCurve;
use snarkvm_circuit_environment::prelude::*;
use snarkvm_circuit_types_boolean::Boolean;
use snarkvm_circuit_types_field::Field;
use snarkvm_circuit_types_scalar::Scalar;
use snarkvm_curves::TwistedEdwardsParameters;

#[derive(Clone)]
pub struct Group<E: Environment> {
    x: Field<E>,
    y: Field<E>,
}

impl<E: Environment> GroupTrait<Scalar<E>> for Group<E> {}

#[cfg(console)]
impl<E: Environment> Inject for Group<E> {
    type Primitive = console::Group<E::Network>;

    /// Initializes a new affine group element.
    ///
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    /// regardless of whether the y-coordinate was recovered.
    fn new(mode: Mode, group: Self::Primitive) -> Self {
        // Initialize the x- and y-coordinate field elements.
        let (x, y) = group.to_xy_coordinate();
        let x = Field::new(mode, x);
        let y = Field::new(mode, y);

        Self::from_xy_coordinates(x, y)
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
        console::Group::from_xy_coordinates((self.x.eject_value(), self.y.eject_value()))
    }
}

#[cfg(console)]
impl<E: Environment> Parser for Group<E> {
    /// Parses a string into a group circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // // Parse the group from the string.
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
        // Constant variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut test_rng());

            Circuit::scope(&format!("Constant {}", i), || {
                let affine = Group::<Circuit>::new(Mode::Constant, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(4, 0, 0, 0);
            });
        }

        // Public variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut test_rng());

            Circuit::scope(&format!("Public {}", i), || {
                let affine = Group::<Circuit>::new(Mode::Public, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(2, 2, 2, 3);
            });
        }

        // Private variables
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut test_rng());

            Circuit::scope(&format!("Private {}", i), || {
                let affine = Group::<Circuit>::new(Mode::Private, point);
                assert_eq!(point, affine.eject_value());
                assert_scope!(2, 0, 4, 3);
            });
        }
    }

    #[test]
    fn test_display() {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let point = Uniform::rand(&mut test_rng());

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

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for _ in 0..ITERATIONS {
                let point = Uniform::rand(&mut test_rng());
                let expected = Group::<Circuit>::new(mode, point);

                let (_, candidate) = Group::<Circuit>::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }
}
