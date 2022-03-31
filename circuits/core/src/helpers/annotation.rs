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

use crate::{Identifier, LiteralType};
use snarkvm_circuits_types::prelude::*;

/// An annotation defines the type parameters for a function or template.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Annotation<E: Environment> {
    /// A literal annotation contains its type name and mode.
    /// The format of the annotation is `<type_name>.<mode>`.
    Literal(LiteralType<E>),
    /// A composite annotation contains its identifier.
    /// The format of the annotation is `<identifier>`.
    Composite(Identifier<E>),
}

impl<E: Environment> Annotation<E> {
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

impl<E: Environment> Parser for Annotation<E> {
    type Environment = E;

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

impl<E: Environment> fmt::Display for Annotation<E> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_annotation_parse() {
        assert_eq!(
            Annotation::parse("field.private"),
            Ok(("", Annotation::<E>::Literal(LiteralType::Field(Mode::Private))))
        );
        assert_eq!(Annotation::parse("signature"), Ok(("", Annotation::<E>::Composite(Identifier::new("signature")))));
    }

    #[test]
    fn test_annotation_parse_fails() {
        // Type must not contain a keyword.
        assert!(Annotation::<E>::parse("field").is_err());
        // Composite must not contain visibility.
        assert_eq!(Ok((".private", Identifier::<E>::new("signature"))), Identifier::<E>::parse("signature.private"));
    }

    #[test]
    fn test_annotation_display() {
        assert_eq!(Annotation::<E>::Literal(LiteralType::Field(Mode::Private)).to_string(), "field.private");
        assert_eq!(Annotation::<E>::Composite(Identifier::new("signature")).to_string(), "signature");
    }

    #[test]
    fn test_annotation_is_literal() {
        assert!(Annotation::<E>::Literal(LiteralType::Field(Mode::Private)).is_literal());
        assert!(!Annotation::<E>::Composite(Identifier::new("signature")).is_literal());
    }

    #[test]
    fn test_annotation_is_composite() {
        assert!(!Annotation::<E>::Literal(LiteralType::Field(Mode::Private)).is_composite());
        assert!(Annotation::<E>::Composite(Identifier::new("signature")).is_composite());
    }
}
