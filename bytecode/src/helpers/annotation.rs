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

use crate::{Identifier, LiteralType, Program};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

/// An annotation defines the type parameter for a register.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Annotation<P: Program> {
    /// A literal annotation contains its type name and mode.
    /// The format of the annotation is `<type_name>.<mode>`.
    Literal(LiteralType<P>),
    /// A composite annotation contains its identifier.
    /// The format of the annotation is `<identifier>`.
    Composite(Identifier<P>),
}

impl<P: Program> Annotation<P> {
    /// Returns `true` if the annotation is a literal.
    /// Returns `false` if the annotation is a composite.
    pub fn is_literal(&self) -> bool {
        matches!(self, Annotation::Literal(..))
    }

    /// Returns `true` if the annotation is a composite.
    /// Returns `false` if the annotation is a literal.
    pub fn is_composite(&self) -> bool {
        matches!(self, Annotation::Composite(..))
    }
}

impl<P: Program> Parser for Annotation<P> {
    type Environment = P::Environment;

    /// Parses a string into an annotation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the annotation (order matters).
        alt((
            map(LiteralType::parse, |type_| Self::Literal(type_)),
            map(Identifier::parse, |identifier| Self::Composite(identifier)),
        ))(string)
    }
}

impl<P: Program> fmt::Display for Annotation<P> {
    /// Prints the annotation as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the type, i.e. field.private
            Self::Literal(type_) => fmt::Display::fmt(type_, f),
            // Prints the composite type, i.e. signature
            Self::Composite(identifier) => fmt::Display::fmt(identifier, f),
        }
    }
}

impl<P: Program> FromBytes for Annotation<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Literal(LiteralType::read_le(&mut reader)?)),
            1 => Ok(Self::Composite(Identifier::read_le(&mut reader)?)),
            2.. => Err(error(format!("Failed to deserialize annotation variant {variant}"))),
        }
    }
}

impl<P: Program> ToBytes for Annotation<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal_type) => {
                u8::write_le(&0u8, &mut writer)?;
                literal_type.write_le(&mut writer)
            }
            Self::Composite(identifier) => {
                u8::write_le(&1u8, &mut writer)?;
                identifier.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Process;

    type P = Process;

    #[test]
    fn test_annotation_parse() {
        assert_eq!(
            Annotation::parse("field.private"),
            Ok(("", Annotation::<P>::Literal(LiteralType::Field(Mode::Private))))
        );
        assert_eq!(
            Annotation::parse("signature"),
            Ok(("", Annotation::<P>::Composite(Identifier::from_str("signature"))))
        );
    }

    #[test]
    fn test_annotation_parse_fails() {
        // Type must not contain a keyword.
        assert!(Annotation::<P>::parse("field").is_err());
        // Composite must not contain visibility.
        assert_eq!(
            Ok((".private", Identifier::<P>::from_str("signature"))),
            Identifier::<P>::parse("signature.private")
        );
    }

    #[test]
    fn test_annotation_display() {
        assert_eq!(Annotation::<P>::Literal(LiteralType::Field(Mode::Private)).to_string(), "field.private");
        assert_eq!(Annotation::<P>::Composite(Identifier::from_str("signature")).to_string(), "signature");
    }

    #[test]
    fn test_annotation_is_literal() {
        assert!(Annotation::<P>::Literal(LiteralType::Field(Mode::Private)).is_literal());
        assert!(!Annotation::<P>::Composite(Identifier::from_str("signature")).is_literal());
    }

    #[test]
    fn test_annotation_is_composite() {
        assert!(!Annotation::<P>::Literal(LiteralType::Field(Mode::Private)).is_composite());
        assert!(Annotation::<P>::Composite(Identifier::from_str("signature")).is_composite());
    }
}
