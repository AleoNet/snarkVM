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

use crate::{helpers::Register, Annotation, Program, Sanitizer};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use std::io::{Read, Result as IoResult, Write};

/// An output statement defines an output of a function, and may refer to the value
/// in either a register or a register member. An output statement is of the form
/// `output {register} as {annotation};`.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Output<P: Program> {
    /// The output register.
    register: Register<P>,
    /// The output annotation.
    annotation: Annotation<P>,
}

impl<P: Program> Output<P> {
    /// Returns the output register.
    #[inline]
    pub fn register(&self) -> &Register<P> {
        &self.register
    }

    /// Returns the output annotation.
    #[inline]
    pub fn annotation(&self) -> &Annotation<P> {
        &self.annotation
    }
}

impl<P: Program> TypeName for Output<P> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "output"
    }
}

impl<P: Program> Parser for Output<P> {
    type Environment = P::Environment;

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

impl<P: Program> fmt::Display for Output<P> {
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

impl<P: Program> FromBytes for Output<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let register = FromBytes::read_le(&mut reader)?;
        let annotation = FromBytes::read_le(&mut reader)?;
        Ok(Self { register, annotation })
    }
}

impl<P: Program> ToBytes for Output<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.register.write_le(&mut writer)?;
        self.annotation.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Process;

    type P = Process;

    #[test]
    fn test_output_type_name() {
        assert_eq!(Output::<P>::type_name(), "output");
    }

    #[test]
    fn test_output_parse() {
        // Literal
        let output = Output::<P>::parse("output r0 as field.private;").unwrap().1;
        assert_eq!(output.register(), &Register::<P>::Locator(0));
        assert_eq!(output.annotation(), &Annotation::<P>::from_str("field.private"));

        // Composite
        let output = Output::<P>::parse("output r1 as signature;").unwrap().1;
        assert_eq!(output.register(), &Register::<P>::Locator(1));
        assert_eq!(output.annotation(), &Annotation::<P>::from_str("signature"));
    }

    #[test]
    fn test_output_display() {
        // Literal
        let output = Output::<P>::parse("output r0 as field.private;").unwrap().1;
        assert_eq!(format!("{}", output), "output r0 as field.private;");

        // Composite
        let output = Output::<P>::parse("output r1 as signature;").unwrap().1;
        assert_eq!(format!("{}", output), "output r1 as signature;");
    }
}
