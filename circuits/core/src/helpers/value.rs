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

use crate::{Annotation, Identifier, Literal, LiteralType};
use snarkvm_circuits_types::prelude::*;

use core::fmt;

/// A value contains the underlying literal(s) in memory.
#[derive(Clone, Debug)]
pub enum Value<E: Environment> {
    /// A literal contains its declared literal value.
    Literal(Literal<E>),
    /// A composite contains its declared member values.
    Composite(Identifier<E>, Vec<Value<E>>),
}

impl<E: Environment> Value<E> {
    /// Returns the annotation.
    #[inline]
    pub fn annotation(&self) -> Annotation<E> {
        match self {
            Self::Literal(literal) => Annotation::Literal(LiteralType::from(literal)),
            Self::Composite(name, _) => Annotation::Composite(name.clone()),
        }
    }

    /// Returns `true` if the value is a constant.
    #[inline]
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Literal(literal) => literal.is_constant(),
            Self::Composite(_, composite) => composite.iter().all(|value| value.is_constant()),
        }
    }
}

impl<E: Environment> Parser for Value<E> {
    type Environment = E;

    /// Parses a string into a value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // TODO (howardwu): Sanitize of any whitespaces, or support whitespaces.
        // Parses a sequence of form: value value ... value
        let sequence_parse = map(pair(pair(many0(Value::parse), tag(" ")), Value::parse), |((values, _), value)| {
            let mut values = values;
            values.push(value);
            values
        });
        // Parses a composite of form: name value value ... value
        let composite_parser = map(pair(pair(Identifier::parse, tag(" ")), sequence_parse), |((name, _), values)| {
            Self::Composite(name, values)
        });

        // Parse to determine the value (order matters).
        alt((map(Literal::parse, |literal| Self::Literal(literal)), composite_parser))(string)
    }
}

impl<E: Environment> fmt::Display for Value<E> {
    /// Prints the value as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. 10field.private
            Self::Literal(literal) => fmt::Display::fmt(literal, f),
            // Prints the composite, i.e. message aleo1xxx.public 10i64.private
            Self::Composite(name, composite) => {
                let mut output = format!("{name} ");
                for value in composite.iter() {
                    output += &format!("{value} ");
                }
                output.pop(); // trailing space
                write!(f, "{output}")
            }
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use snarkvm_circuits_types::environment::Circuit;
//
//     type E = Circuit;
//
//     #[test]
//     fn test_value_parse() {
//         // Test parsing a literal.
//         assert_eq!(
//             Value::<E>::Literal(Literal::from_str("10field.private")),
//             Value::parse("10field.private").unwrap().1,
//         );
//
//         // Test parsing a composite.
//         assert_eq!(
//             Value::<E>::Composite(Identifier::from_str("message"), vec![
//                 Value::<E>::Literal(Literal::from_str("2group.public")),
//                 Value::<E>::Literal(Literal::from_str("10field.private")),
//             ]),
//             Value::parse("message 2group.public 10field.private").unwrap().1,
//         );
//     }
// }
