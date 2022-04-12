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
pub mod compare;
pub mod div;
pub mod double;
pub mod equal;
pub mod from_bits;
pub mod from_boolean;
pub mod inv;
pub mod mul;
pub mod neg;
pub mod one;
pub mod pow;
pub mod square;
pub mod sub;
pub mod ternary;
pub mod to_bits;
pub mod to_lower_bits;
pub mod to_upper_bits;
pub mod zero;

#[cfg(test)]
use snarkvm_circuits_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types_boolean::Boolean;
use snarkvm_utilities::ToBits as TBits;

#[derive(Clone)]
pub struct Field<E: Environment> {
    /// The linear combination contains the primary representation of the field.
    linear_combination: LinearCombination<E::BaseField>,
    /// An optional secondary representation in little-endian bits is provided,
    /// so that calls to `ToBits` only incur constraint costs once.
    bits_le: OnceCell<Vec<Boolean<E>>>,
}

impl<E: Environment> FieldTrait for Field<E> {}

impl<E: Environment> Inject for Field<E> {
    type Primitive = E::BaseField;

    ///
    /// Initializes a new instance of a base field from a primitive base field value.
    ///
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        Self { linear_combination: E::new_variable(mode, value).into(), bits_le: Default::default() }
    }
}

impl<E: Environment> Eject for Field<E> {
    type Primitive = E::BaseField;

    ///
    /// Ejects the mode of the base field.
    ///
    fn eject_mode(&self) -> Mode {
        self.linear_combination.mode()
    }

    ///
    /// Ejects the base field as a constant base field value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        self.linear_combination.value()
    }
}

impl<E: Environment> Parser for Field<E> {
    type Environment = E;

    /// Parses a string into a base field circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the value from the string.
        let (string, value): (&str, E::BaseField) =
            map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;
        // Negate the value if the negative sign was present.
        let value = match negation {
            true => -value,
            false => value,
        };

        match mode {
            Some((_, mode)) => Ok((string, Field::new(mode, value))),
            None => Ok((string, Field::new(Mode::Constant, value))),
        }
    }
}

impl<E: Environment> TypeName for Field<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        "field"
    }
}

impl<E: Environment> Debug for Field<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> Display for Field<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}.{}", self.eject_value(), Self::type_name(), self.eject_mode())
    }
}

impl<E: Environment> From<LinearCombination<E::BaseField>> for Field<E> {
    fn from(linear_combination: LinearCombination<E::BaseField>) -> Self {
        Self { linear_combination, bits_le: Default::default() }
    }
}

impl<E: Environment> From<&LinearCombination<E::BaseField>> for Field<E> {
    fn from(linear_combination: &LinearCombination<E::BaseField>) -> Self {
        From::from(linear_combination.clone())
    }
}

impl<E: Environment> From<Field<E>> for LinearCombination<E::BaseField> {
    fn from(field: Field<E>) -> Self {
        From::from(&field)
    }
}

impl<E: Environment> From<&Field<E>> for LinearCombination<E::BaseField> {
    fn from(field: &Field<E>) -> Self {
        field.linear_combination.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::str::FromStr;

    const ITERATIONS: usize = 10_000;

    /// Attempts to construct a field from the given element and mode,
    /// format it in debug mode, and recover a field from it.
    fn check_debug(mode: Mode, element: <Circuit as Environment>::BaseField) {
        let candidate = Field::<Circuit>::new(mode, element);
        assert_eq!(element.to_string(), format!("{:?}", candidate));

        let candidate_element = <Circuit as Environment>::BaseField::from_str(&format!("{:?}", candidate)).unwrap();
        let candidate_recovered = Field::<Circuit>::new(mode, candidate_element);
        assert_eq!(candidate.eject_value(), candidate_recovered.eject_value());
    }

    #[test]
    fn test_debug() {
        for _ in 0..ITERATIONS {
            let element = UniformRand::rand(&mut test_rng());

            // Constant
            check_debug(Mode::Constant, element);
            // Public
            check_debug(Mode::Public, element);
            // Private
            check_debug(Mode::Private, element);
        }
    }

    #[test]
    fn test_debug_zero() {
        let zero = <Circuit as Environment>::BaseField::zero();

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, zero);
        assert_eq!("0", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_one() {
        let one = <Circuit as Environment>::BaseField::one();

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, one);
        assert_eq!("1", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_two() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, two);
        assert_eq!("2", &format!("{:?}", candidate));
    }

    #[test]
    fn test_parser() {
        type Primitive = <Circuit as Environment>::BaseField;

        // Constant

        let (_, candidate) = Field::<Circuit>::parse("5field").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::<Circuit>::parse("5_field").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::<Circuit>::parse("1_5_field").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::<Circuit>::parse("5field.constant").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::<Circuit>::parse("5_field.constant").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::<Circuit>::parse("1_5_field.constant").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        // Public

        let (_, candidate) = Field::<Circuit>::parse("5field.public").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Field::<Circuit>::parse("5_field.public").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Field::<Circuit>::parse("1_5_field.public").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        // Private

        let (_, candidate) = Field::<Circuit>::parse("5field.private").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Field::<Circuit>::parse("5_field.private").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Field::<Circuit>::parse("1_5_field.private").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        // Random

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for _ in 0..ITERATIONS {
                let value: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
                let expected = Field::<Circuit>::new(mode, value);

                let (_, candidate) = Field::<Circuit>::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }

    #[test]
    fn test_display() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2field.constant", &format!("{}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, two);
        assert_eq!("2field.public", &format!("{}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, two);
        assert_eq!("2field.private", &format!("{}", candidate));
    }
}
