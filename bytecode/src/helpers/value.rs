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

use crate::{Annotation, Identifier, LiteralType};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use std::io::{Read, Result as IoResult, Write};

/// A value contains the underlying literal(s) in memory.
#[derive(Clone, Debug)]
pub enum Value<E: Environment> {
    /// A literal contains its declared literal value.
    Literal(Literal<E>),
    /// A composite contains its declared member literals.
    Composite(Identifier<E>, Vec<Literal<E>>),
}

impl<E: Environment> From<Literal<E>> for Value<E> {
    fn from(literal: Literal<E>) -> Self {
        Value::Literal(literal)
    }
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
            Self::Composite(_, members) => members.iter().all(|literal| literal.is_constant()),
        }
    }
}

impl<E: Environment> Parser for Value<E> {
    type Environment = E;

    /// Parses a string into a value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parses a sequence of form: literal literal ... literal
        let sequence_parse =
            map(pair(pair(many0(Literal::parse), tag(" ")), Literal::parse), |((literals, _), literal)| {
                let mut literals = literals;
                literals.push(literal);
                literals
            });
        // Parses a composite of form: name literal literal ... literal
        let composite_parser = map(pair(pair(Identifier::parse, tag(" ")), sequence_parse), |((name, _), literals)| {
            Self::Composite(name, literals)
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
            Self::Composite(name, members) => {
                let mut output = format!("{name} ");
                for value in members.iter() {
                    output += &format!("{value} ");
                }
                output.pop(); // trailing space
                write!(f, "{output}")
            }
        }
    }
}

impl<E: Environment> FromBytes for Value<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Literal(Literal::read_le(&mut reader)?)),
            1 => {
                // Read the name.
                let name = Identifier::read_le(&mut reader)?;
                // Read the members.
                let num_members = u16::read_le(&mut reader)?;
                let mut members = Vec::with_capacity(num_members as usize);
                for _ in 0..num_members {
                    members.push(Literal::read_le(&mut reader)?);
                }
                Ok(Self::Composite(name, members))
            }
            variant => Err(error(format!("Failed to deserialize value variant {variant}"))),
        }
    }
}

impl<E: Environment> ToBytes for Value<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal) => {
                u8::write_le(&0u8, &mut writer)?;
                literal.write_le(&mut writer)
            }
            Self::Composite(name, members) => {
                u8::write_le(&1u8, &mut writer)?;
                name.write_le(&mut writer)?;
                (members.len() as u16).write_le(&mut writer)?;
                members.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)] // Do not remove this. It is not a performant way to compare values.
impl<E: Environment> PartialEq for Value<E> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Literal(literal), Self::Literal(other_literal)) => literal.eject() == other_literal.eject(),
            (Self::Composite(name, members), Self::Composite(other_name, other_members)) => {
                name == other_name && members.eject() == other_members.eject()
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_value_parse() {
        // Test parsing a literal.
        assert_eq!(
            Value::<E>::Literal(Literal::from_str("10field.private")),
            Value::parse("10field.private").unwrap().1,
        );

        // Test parsing a composite.
        assert_eq!(
            Value::<E>::Composite(Identifier::from_str("message"), vec![
                Literal::from_str("2group.public"),
                Literal::from_str("10field.private"),
            ]),
            Value::parse("message 2group.public 10field.private").unwrap().1,
        );
    }
}
