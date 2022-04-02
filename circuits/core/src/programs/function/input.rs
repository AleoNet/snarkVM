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

use crate::{helpers::Register, Annotation, Sanitizer};
use snarkvm_circuits_types::prelude::*;
use snarkvm_utilities::error;

use core::{cmp::Ordering, fmt};

/// An input statement defines an input argument to a function, and is of the form
/// `input {register} as {annotation}`.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Input<E: Environment> {
    /// The input register.
    register: Register<E>,
    /// The input annotation.
    annotation: Annotation<E>,
}

impl<E: Environment> Input<E> {
    /// Returns the input register.
    #[inline]
    pub fn register(&self) -> &Register<E> {
        &self.register
    }

    /// Returns the input annotation.
    #[inline]
    pub fn annotation(&self) -> &Annotation<E> {
        &self.annotation
    }
}

impl<E: Environment> TypeName for Input<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "input"
    }
}

impl<E: Environment> Parser for Input<E> {
    type Environment = E;

    /// Parses a string into an input statement.
    /// The input statement is of the form `input {register} as {annotation};`.
    ///
    /// # Errors
    /// This function will halt if the given register is a register member.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the input keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the register from the string.
        let (string, register) = map_res(Register::parse, |register| {
            // Ensure the register is not a register member.
            match &register {
                Register::Locator(..) => Ok(register),
                Register::Member(..) => Err(error(format!("Input register {register} cannot be a register member"))),
            }
        })(string)?;
        // Parse the " as " from the string.
        let (string, _) = tag(" as ")(string)?;
        // Parse the annotation from the string.
        let (string, annotation) = Annotation::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the input statement.
        Ok((string, Self { register, annotation }))
    }
}

impl<E: Environment> fmt::Display for Input<E> {
    /// Prints the input statement as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{type_} {register} as {annotation};",
            type_ = Self::type_name(),
            register = self.register,
            annotation = self.annotation
        )
    }
}

impl<E: Environment> Ord for Input<E> {
    /// Ordering is determined by the register (the annotation is ignored).
    fn cmp(&self, other: &Self) -> Ordering {
        self.register().cmp(other.register())
    }
}

impl<E: Environment> PartialOrd for Input<E> {
    /// Ordering is determined by the register (the annotation is ignored).
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_input_type_name() {
        assert_eq!(Input::<E>::type_name(), "input");
    }

    #[test]
    fn test_input_parse() {
        // Literal
        let input = Input::<E>::parse("input r0 as field.private;").unwrap().1;
        assert_eq!(input.register(), &Register::<E>::Locator(0));
        assert_eq!(input.annotation(), &Annotation::<E>::from_str("field.private"));

        // Composite
        let input = Input::<E>::parse("input r1 as signature;").unwrap().1;
        assert_eq!(input.register(), &Register::<E>::Locator(1));
        assert_eq!(input.annotation(), &Annotation::<E>::from_str("signature"));
    }

    #[test]
    fn test_input_display() {
        // Literal
        let input = Input::<E>::from_str("input r0 as field.private;");
        assert_eq!("input r0 as field.private;", input.to_string());

        // Composite
        let input = Input::<E>::from_str("input r1 as signature;");
        assert_eq!("input r1 as signature;", input.to_string());
    }

    #[test]
    fn test_input_partial_ord() {
        let input1 = Input::<E>::from_str("input r0 as field.private;");
        let input2 = Input::<E>::from_str("input r1 as field.private;");

        let input3 = Input::<E>::from_str("input r0 as signature;");
        let input4 = Input::<E>::from_str("input r1 as signature;");

        assert_eq!(input1.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input1.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input4), Some(Ordering::Less));

        assert_eq!(input2.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input2.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input4), Some(Ordering::Equal));

        assert_eq!(input3.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input3.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input4), Some(Ordering::Less));

        assert_eq!(input4.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input4.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input4), Some(Ordering::Equal));
    }
}
