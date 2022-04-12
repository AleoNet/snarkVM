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
pub mod equal;
pub mod from_bits;
pub mod one;
pub mod ternary;
pub mod to_bits;
pub mod to_field;
pub mod to_fields;
pub mod zero;

#[cfg(test)]
use snarkvm_circuits_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types_boolean::Boolean;
use snarkvm_circuits_types_field::Field;
use snarkvm_utilities::{FromBits as FBits, ToBits as TBits};

#[derive(Clone)]
pub struct Scalar<E: Environment> {
    /// The little-endian bit representation of the scalar.
    bits_le: Vec<Boolean<E>>,
}

impl<E: Environment> ScalarTrait for Scalar<E> {}

impl<E: Environment> Inject for Scalar<E> {
    type Primitive = E::ScalarField;

    /// Initializes a new instance of a scalar field from a primitive scalar field value.
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        Self { bits_le: Inject::new(mode, value.to_bits_le()) }
    }
}

impl<E: Environment> Eject for Scalar<E> {
    type Primitive = E::ScalarField;

    ///
    /// Ejects the mode of the scalar field.
    ///
    fn eject_mode(&self) -> Mode {
        let mut scalar_mode = Mode::Constant;
        for bit_mode in self.bits_le.iter().map(Eject::eject_mode) {
            // Check if the mode in the current iteration matches the scalar mode.
            if scalar_mode != bit_mode {
                // If they do not match, the scalar mode must be a constant.
                // Otherwise, this is a malformed scalar, and the program should halt.
                match scalar_mode == Mode::Constant {
                    true => scalar_mode = bit_mode,
                    false => E::halt("Detected an scalar field with a malformed mode"),
                }
            }
        }
        scalar_mode
    }

    ///
    /// Ejects the scalar field as a constant scalar field value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        let bits = self.bits_le.eject_value();
        let biginteger = <E::ScalarField as PrimeField>::BigInteger::from_bits_le(&bits[..]);
        match <E::ScalarField as PrimeField>::from_repr(biginteger) {
            Some(scalar) => scalar,
            None => E::halt("Failed to eject scalar field value"),
        }
    }
}

impl<E: Environment> Parser for Scalar<E> {
    type Environment = E;

    /// Parses a string into a scalar field circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the value from the string.
        let (string, value): (&str, E::ScalarField) =
            map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;
        // Negate the value if the negative sign was present.
        let value = match negation {
            true => -value,
            false => value,
        };

        match mode {
            Some((_, mode)) => Ok((string, Scalar::new(mode, value))),
            None => Ok((string, Scalar::new(Mode::Constant, value))),
        }
    }
}

impl<E: Environment> TypeName for Scalar<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        "scalar"
    }
}

impl<E: Environment> Debug for Scalar<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> Display for Scalar<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}.{}", self.eject_value(), Self::type_name(), self.eject_mode())
    }
}

impl<E: Environment> From<Scalar<E>> for LinearCombination<E::BaseField> {
    fn from(scalar: Scalar<E>) -> Self {
        From::from(&scalar)
    }
}

impl<E: Environment> From<&Scalar<E>> for LinearCombination<E::BaseField> {
    fn from(scalar: &Scalar<E>) -> Self {
        scalar.to_field().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use core::str::FromStr;

    const ITERATIONS: usize = 250;

    fn check_new(
        name: &str,
        expected: <Circuit as Environment>::ScalarField,
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let candidate = Scalar::<Circuit>::new(mode, expected);
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
    }

    /// Attempts to construct a field from the given element and mode,
    /// format it in debug mode, and recover a field from it.
    fn check_debug(mode: Mode, element: <Circuit as Environment>::ScalarField) {
        let candidate = Scalar::<Circuit>::new(mode, element);
        assert_eq!(element.to_string(), format!("{:?}", candidate));

        let candidate_element = <Circuit as Environment>::ScalarField::from_str(&format!("{:?}", candidate)).unwrap();
        let candidate_recovered = Scalar::<Circuit>::new(mode, candidate_element);
        assert_eq!(candidate.eject_value(), candidate_recovered.eject_value());
    }

    #[test]
    fn test_new_constant() {
        let expected = UniformRand::rand(&mut test_rng());
        check_new("Constant", expected, Mode::Constant, 251, 0, 0, 0);
    }

    #[test]
    fn test_new_public() {
        let expected = UniformRand::rand(&mut test_rng());
        check_new("Public", expected, Mode::Public, 0, 251, 0, 251);
    }

    #[test]
    fn test_new_private() {
        let expected = UniformRand::rand(&mut test_rng());
        check_new("Private", expected, Mode::Private, 0, 0, 251, 251);
    }

    #[test]
    fn test_debug() {
        for _ in 0..ITERATIONS {
            let element: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());

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
        let zero = <Circuit as Environment>::ScalarField::zero();

        // Constant
        let candidate = Scalar::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Public
        let candidate = Scalar::<Circuit>::new(Mode::Public, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Private
        let candidate = Scalar::<Circuit>::new(Mode::Private, zero);
        assert_eq!("0", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_one() {
        let one = <Circuit as Environment>::ScalarField::one();

        // Constant
        let candidate = Scalar::<Circuit>::new(Mode::Constant, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Public
        let candidate = Scalar::<Circuit>::new(Mode::Public, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Private
        let candidate = Scalar::<Circuit>::new(Mode::Private, one);
        assert_eq!("1", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_two() {
        let one = <Circuit as Environment>::ScalarField::one();
        let two = one + one;

        // Constant
        let candidate = Scalar::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Public
        let candidate = Scalar::<Circuit>::new(Mode::Public, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Private
        let candidate = Scalar::<Circuit>::new(Mode::Private, two);
        assert_eq!("2", &format!("{:?}", candidate));
    }

    #[test]
    fn test_parser() {
        type Primitive = <Circuit as Environment>::ScalarField;

        // Constant

        let (_, candidate) = Scalar::<Circuit>::parse("5scalar").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Scalar::<Circuit>::parse("5_scalar").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Scalar::<Circuit>::parse("1_5_scalar").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Scalar::<Circuit>::parse("5scalar.constant").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Scalar::<Circuit>::parse("5_scalar.constant").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Scalar::<Circuit>::parse("1_5_scalar.constant").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_constant());

        // Public

        let (_, candidate) = Scalar::<Circuit>::parse("5scalar.public").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Scalar::<Circuit>::parse("5_scalar.public").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Scalar::<Circuit>::parse("1_5_scalar.public").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_public());

        // Private

        let (_, candidate) = Scalar::<Circuit>::parse("5scalar.private").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Scalar::<Circuit>::parse("5_scalar.private").unwrap();
        assert_eq!(Primitive::from_str("5").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Scalar::<Circuit>::parse("1_5_scalar.private").unwrap();
        assert_eq!(Primitive::from_str("15").unwrap(), candidate.eject_value());
        assert!(candidate.is_private());

        // Random

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for _ in 0..ITERATIONS {
                let value: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
                let expected = Scalar::<Circuit>::new(mode, value);

                let (_, candidate) = Scalar::<Circuit>::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }

    #[test]
    fn test_display() {
        let one = <Circuit as Environment>::ScalarField::one();
        let two = one + one;

        // Constant
        let candidate = Scalar::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2scalar.constant", &format!("{}", candidate));

        // Public
        let candidate = Scalar::<Circuit>::new(Mode::Public, two);
        assert_eq!("2scalar.public", &format!("{}", candidate));

        // Private
        let candidate = Scalar::<Circuit>::new(Mode::Private, two);
        assert_eq!("2scalar.private", &format!("{}", candidate));
    }
}
