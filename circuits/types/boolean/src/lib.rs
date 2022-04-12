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

pub mod adder;
pub mod and;
pub mod equal;
pub mod from_bits;
pub mod nand;
pub mod nor;
pub mod not;
pub mod or;
pub mod subtractor;
pub mod ternary;
pub mod to_bits;
// pub mod to_field;
pub mod xor;

#[cfg(test)]
use snarkvm_circuits_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuits_environment::prelude::*;

use core::ops::Deref;

#[derive(Clone)]
pub struct Boolean<E: Environment>(LinearCombination<E::BaseField>);

impl<E: Environment> BooleanTrait for Boolean<E> {}

impl<E: Environment> Inject for Boolean<E> {
    type Primitive = bool;

    ///
    /// Initializes a new instance of a boolean from a primitive boolean value.
    ///
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        let variable = E::new_variable(mode, match value {
            true => E::BaseField::one(),
            false => E::BaseField::zero(),
        });

        // Ensure (1 - a) * a = 0
        // `a` must be either 0 or 1.
        E::enforce(|| (E::one() - &variable, &variable, E::zero()));

        Self(variable.into())
    }

    ///
    /// Initializes a constant boolean circuit from a primitive boolean value.
    ///
    fn constant(value: Self::Primitive) -> Self {
        match value {
            true => Self(E::one()),
            false => Self(E::zero()),
        }
    }
}

impl<E: Environment> Eject for Boolean<E> {
    type Primitive = bool;

    ///
    /// Ejects the mode of the boolean.
    ///
    fn eject_mode(&self) -> Mode {
        // Perform a software-level safety check that the boolean is well-formed.
        match self.0.is_boolean_type() {
            true => self.0.mode(),
            false => E::halt("Boolean variable is not well-formed"),
        }
    }

    ///
    /// Ejects the boolean as a constant boolean value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        let value = self.0.value();
        debug_assert!(value.is_zero() || value.is_one());
        value.is_one()
    }
}

impl<E: Environment> Parser for Boolean<E> {
    type Environment = E;

    /// Parses a string into a boolean circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the boolean from the string.
        let (string, value) = alt((map(tag("true"), |_| true), map(tag("false"), |_| false)))(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Boolean::new(mode, value))),
            None => Ok((string, Boolean::new(Mode::Constant, value))),
        }
    }
}

impl<E: Environment> TypeName for Boolean<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        "boolean"
    }
}

impl<E: Environment> Debug for Boolean<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> Display for Boolean<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}

impl<E: Environment> Deref for Boolean<E> {
    type Target = LinearCombination<E::BaseField>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Environment> From<Boolean<E>> for LinearCombination<E::BaseField> {
    fn from(boolean: Boolean<E>) -> Self {
        boolean.0
    }
}

impl<E: Environment> From<&Boolean<E>> for LinearCombination<E::BaseField> {
    fn from(boolean: &Boolean<E>) -> Self {
        boolean.0.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    #[test]
    fn test_new_constant() {
        Circuit::scope("test_new_constant", || {
            let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
            assert!(!candidate.eject_value()); // false
            assert_scope!(1, 0, 0, 0);

            let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
            assert!(candidate.eject_value()); // true
            assert_scope!(2, 0, 0, 0);
        });
    }

    #[test]
    fn test_new_public() {
        Circuit::scope("test_new_public", || {
            let candidate = Boolean::<Circuit>::new(Mode::Public, false);
            assert!(!candidate.eject_value()); // false
            assert_scope!(0, 1, 0, 1);

            let candidate = Boolean::<Circuit>::new(Mode::Public, true);
            assert!(candidate.eject_value()); // true
            assert_scope!(0, 2, 0, 2);
        });
    }

    #[test]
    fn test_new_private() {
        Circuit::scope("test_new_private", || {
            let candidate = Boolean::<Circuit>::new(Mode::Private, false);
            assert!(!candidate.eject_value()); // false
            assert_scope!(0, 0, 1, 1);

            let candidate = Boolean::<Circuit>::new(Mode::Private, true);
            assert!(candidate.eject_value()); // true
            assert_scope!(0, 0, 2, 2);
        });
    }

    #[test]
    fn test_new_fail() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;
        {
            let candidate = Circuit::new_variable(Mode::Constant, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            Circuit::enforce(|| (Circuit::one() - &candidate, candidate, Circuit::zero()));
            assert_eq!(0, Circuit::num_constraints());

            Circuit::reset();
        }
        {
            let candidate = Circuit::new_variable(Mode::Public, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            Circuit::enforce(|| (Circuit::one() - &candidate, candidate, Circuit::zero()));
            assert!(!Circuit::is_satisfied());

            Circuit::reset();
        }
        {
            let candidate = Circuit::new_variable(Mode::Private, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            Circuit::enforce(|| (Circuit::one() - &candidate, candidate, Circuit::zero()));
            assert!(!Circuit::is_satisfied());

            Circuit::reset();
        }
    }

    #[test]
    fn test_debug() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        assert_eq!("false", format!("{:?}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        assert_eq!("true", format!("{:?}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        assert_eq!("false", format!("{:?}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        assert_eq!("true", format!("{:?}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        assert_eq!("false", format!("{:?}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        assert_eq!("true", format!("{:?}", candidate));
    }

    #[test]
    fn test_parser() {
        let (_, candidate) = Boolean::<Circuit>::parse("true").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::<Circuit>::parse("false").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::<Circuit>::parse("true.constant").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::<Circuit>::parse("false.constant").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::<Circuit>::parse("true.public").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Boolean::<Circuit>::parse("false.public").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Boolean::<Circuit>::parse("true.private").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Boolean::<Circuit>::parse("false.private").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_private());

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for value in [true, false] {
                let expected = Boolean::<Circuit>::new(mode, value);

                let (_, candidate) = Boolean::<Circuit>::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }

    #[test]
    fn test_display() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        assert_eq!("false.constant", format!("{}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        assert_eq!("true.constant", format!("{}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        assert_eq!("false.public", format!("{}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        assert_eq!("true.public", format!("{}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        assert_eq!("false.private", format!("{}", candidate));

        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        assert_eq!("true.private", format!("{}", candidate));
    }
}
