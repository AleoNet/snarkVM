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

use crate::program::{helpers::Register, Annotation, Sanitizer};
use snarkvm_circuits_types::prelude::*;

use core::fmt;

/// An output statement defines an output of a function, and may refer to the value
/// in either a register or a register member. An output statement is of the form
/// `output {register} as {annotation};`.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Output<E: Environment> {
    /// The output register.
    register: Register<E>,
    /// The output annotation.
    annotation: Annotation<E>,
}

impl<E: Environment> Output<E> {
    /// Returns the output register.
    #[inline]
    pub fn register(&self) -> &Register<E> {
        &self.register
    }

    /// Returns the output annotation.
    #[inline]
    pub fn annotation(&self) -> &Annotation<E> {
        &self.annotation
    }
}

impl<E: Environment> TypeName for Output<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "output"
    }
}

impl<E: Environment> Parser for Output<E> {
    type Environment = E;

    /// Parses a string into an output statement.
    /// The output statement is of the form `output {register} as {annotation};`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the output keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the register from the string.
        let (string, register) = Register::parse(string)?;
        // Parse the " as " from the string.
        let (string, _) = tag(" as ")(string)?;
        // Parse the annotation from the string.
        let (string, annotation) = Annotation::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the output statement.
        Ok((string, Self { register, annotation }))
    }
}

impl<E: Environment> fmt::Display for Output<E> {
    /// Prints the output statement as a string.
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

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_output_type_name() {
        assert_eq!(Output::<E>::type_name(), "output");
    }

    #[test]
    fn test_output_parse() {
        // Literal
        let output = Output::<E>::parse("output r0 as field.private;").unwrap().1;
        assert_eq!(output.register(), &Register::<E>::Locator(0));
        assert_eq!(output.annotation(), &Annotation::<E>::from_str("field.private"));

        // Composite
        let output = Output::<E>::parse("output r1 as signature;").unwrap().1;
        assert_eq!(output.register(), &Register::<E>::Locator(1));
        assert_eq!(output.annotation(), &Annotation::<E>::from_str("signature"));
    }

    #[test]
    fn test_output_display() {
        // Literal
        let output = Output::<E>::parse("output r0 as field.private;").unwrap().1;
        assert_eq!(format!("{}", output), "output r0 as field.private;");

        // Composite
        let output = Output::<E>::parse("output r1 as signature;").unwrap().1;
        assert_eq!(format!("{}", output), "output r1 as signature;");
    }
}
