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

use crate::{variable_length::*, Annotation, Identifier, LiteralType, Program, Sanitizer};
use snarkvm_circuit::prelude::*;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use nom::{combinator::fail, multi::separated_list1};
use std::io::{Read, Result as IoResult, Write};

/// A value contains the underlying literal(s) in memory.
#[derive(Clone, Debug)]
pub enum Value<P: Program> {
    /// A literal contains its declared literal value.
    Literal(Literal<P::Environment>),
    /// A definition contains its identifier and declared member values.
    Definition(Identifier<P>, Vec<Value<P>>),
}

impl<P: Program> From<Literal<P::Environment>> for Value<P> {
    fn from(literal: Literal<P::Environment>) -> Self {
        Value::Literal(literal)
    }
}

impl<P: Program> Value<P> {
    /// Returns a list of literals.
    #[inline]
    pub fn to_literals(&self) -> Vec<Literal<P::Environment>> {
        match self {
            Value::Literal(literal) => vec![(*literal).clone()],
            Value::Definition(name, values) => [Literal::String(name.to_string_constant())]
                .into_iter()
                .chain(values.iter().cloned().flat_map(|value| value.to_literals()))
                .collect(),
        }
    }

    /// Returns the annotation.
    #[inline]
    pub fn annotation(&self) -> Annotation<P> {
        match self {
            Self::Literal(literal) => Annotation::Literal(LiteralType::from(literal)),
            Self::Definition(name, _) => Annotation::Definition(name.clone()),
        }
    }

    /// Returns `true` if the value is a constant.
    #[inline]
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Literal(literal) => literal.is_constant(),
            Self::Definition(_, members) => members.iter().all(|value| value.is_constant()),
        }
    }
}

impl<P: Program> Parser for Value<P> {
    type Environment = P::Environment;

    /// Parses a string into a value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Helper function to parse a value.
        /// The parameter `depth` is used to track the current recursive depth of a value definition.
        fn parse_value<'a, P: Program>(string: &'a str, depth: usize) -> ParserResult<Value<P>> {
            match depth <= P::NUM_DEPTH {
                false => fail(string),
                true => {
                    /// Parses a value definition as `name { member_0, member_1, ..., member_n }`.
                    fn parse_definition<'a, P: Program>(string: &'a str, depth: usize) -> ParserResult<Value<P>> {
                        /// Parses a sanitized member.
                        fn parse_sanitized_member<P: Program>(string: &str, depth: usize) -> ParserResult<Value<P>> {
                            // Parse the whitespace and comments from the string.
                            let (string, _) = Sanitizer::parse(string)?;
                            // Increment the depth and parse the annotation from the string.
                            parse_value(string, depth + 1)
                        }

                        // Parse the name from the string.
                        let (string, name) = Identifier::parse(string)?;
                        // Parse the " {" from the string.
                        let (string, _) = tag(" {")(string)?;
                        // Parse the members.
                        let (string, members) = map_res(
                            separated_list1(tag(","), |string: &'a str| parse_sanitized_member(string, depth)),
                            |members: Vec<Value<P>>| {
                                // Ensure the number of members is within `P::NUM_DEPTH`.
                                if members.len() <= P::NUM_DEPTH {
                                    Ok(members)
                                } else {
                                    Err(error(format!("Detected a value with too many members ({})", members.len())))
                                }
                            },
                        )(string)?;
                        // Parse the whitespace and comments from the string.
                        let (string, _) = Sanitizer::parse(string)?;
                        // Parse the '}' from the string.
                        let (string, _) = tag("}")(string)?;
                        // Output the value.
                        Ok((string, Value::Definition(name, members)))
                    }

                    // Parse to determine the value (order matters).
                    alt((
                        // Parse a value literal.
                        map(Literal::parse, |literal| Value::Literal(literal)),
                        // Parse a value definition.
                        |string: &'a str| parse_definition(string, depth),
                    ))(string)
                }
            }
        }
        parse_value(string, 0)
    }
}

#[allow(clippy::format_push_string)]
impl<P: Program> fmt::Display for Value<P> {
    /// Prints the value as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. 10field.private
            Self::Literal(literal) => fmt::Display::fmt(literal, f),
            // Prints the definition, i.e. message { aleo1xxx.public, 10i64.private }
            Self::Definition(name, members) => {
                let mut output = format!("{name} {{ ");
                for value in members.iter() {
                    output += &format!("{value}, ");
                }
                output.pop(); // trailing space
                output.pop(); // trailing comma
                output += " }";
                write!(f, "{output}")
            }
        }
    }
}

impl<P: Program> FromBytes for Value<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => {
                let mode = Mode::read_le(&mut reader)?;
                let primitive = snarkvm_console_program::Literal::read_le(&mut reader)?;
                Ok(Self::Literal(Literal::new(mode, primitive)))
            }
            1 => {
                // Read the name.
                let name = Identifier::read_le(&mut reader)?;
                // Read the members.
                let num_members = u16::read_le(&mut reader)?;
                let mut members = Vec::with_capacity(num_members as usize);
                for _ in 0..num_members {
                    // Read the number of bytes for the member.
                    let num_bytes = read_variable_length_integer(&mut reader)?;
                    // Read the member.
                    let mut bytes = vec![0; num_bytes as usize];
                    reader.read_exact(&mut bytes)?;
                    members.push(Value::read_le(&mut bytes.as_slice())?);
                }
                Ok(Self::Definition(name, members))
            }
            2.. => Err(error(format!("Failed to deserialize value variant {variant}"))),
        }
    }
}

impl<P: Program> ToBytes for Value<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal) => {
                u8::write_le(&0u8, &mut writer)?;
                literal.eject_mode().write_le(&mut writer)?;
                literal.eject_value().write_le(&mut writer)
            }
            Self::Definition(name, members) => {
                // Ensure the number of members is within `P::NUM_DEPTH`.
                if members.len() > P::NUM_DEPTH {
                    return Err(error("Failed to serialize value: too many members"));
                }

                // Write the variant.
                u8::write_le(&1u8, &mut writer)?;
                // Write the name.
                name.write_le(&mut writer)?;
                // Write the number of members.
                (members.len() as u16).write_le(&mut writer)?;
                // Write the members as bytes.
                for member in members {
                    match member.to_bytes_le() {
                        Ok(bytes) => {
                            variable_length_integer(&(bytes.len() as u64)).write_le(&mut writer)?;
                            bytes.write_le(&mut writer)?;
                        }
                        Err(err) => return Err(error(format!("{err}"))),
                    }
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)] // Do not remove the `#[cfg(test)]`. It is not a performant way to compare values.
impl<P: Program> PartialEq for Value<P> {
    fn eq(&self, other: &Self) -> bool {
        self.to_bytes_le().unwrap() == other.to_bytes_le().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Process;

    type P = Process;

    // Helper function to create a value definition of desired depth greater than zero.
    fn create_random_value_definition(depth: usize) -> Value<P> {
        match depth {
            depth if depth == 0 => panic!("Cannot create a value definition with depth 0"),
            depth if depth == 1 => Value::<P>::Definition(Identifier::from_str("child_1"), vec![Value::<P>::Literal(
                Literal::from_str("0field.private"),
            )]),
            _ => Value::<P>::Definition(Identifier::from_str(format!("child_{}", depth).as_str()), vec![
                create_random_value_definition(depth - 1),
            ]),
        }
    }

    #[test]
    fn test_value_parse() {
        // Test parsing a value literal.
        assert_eq!(
            Value::<P>::Literal(Literal::from_str("10field.private")),
            Value::parse("10field.private").unwrap().1,
        );

        // Test parsing a value definition.
        assert_eq!(
            Value::<P>::Definition(Identifier::from_str("message"), vec![
                Value::from_str("2group.public"),
                Value::from_str("10field.private"),
            ]),
            Value::parse("message { 2group.public, 10field.private }").unwrap().1,
        );

        // Test parsing a value definition with a nested definition.
        assert_eq!(
            Value::<P>::Definition(Identifier::from_str("message"), vec![
                Value::from_str("2group.public"),
                Value::from_str("10field.private"),
                Value::<P>::Definition(Identifier::from_str("signature"), vec![
                    Value::from_str("5scalar.public"),
                    Value::from_str("3scalar.private"),
                ]),
                Value::from_str("true.public"),
            ]),
            Value::parse(
                "message { 2group.public, 10field.private, signature { 5scalar.public, 3scalar.private }, true.public }"
            )
            .unwrap()
            .1,
        );
    }

    #[test]
    fn test_value_to_string() {
        // Test a value literal.
        let expected = "10field.private";
        let value = Value::<P>::parse(expected).unwrap().1;
        assert_eq!(expected, value.to_string());

        // Test a value definition.
        let expected = "message { 2group.public, 10field.private }";
        let value = Value::<P>::parse(expected).unwrap().1;
        assert_eq!(expected, value.to_string());

        // Test a value definition with a nested definition.
        let expected =
            "message { 2group.public, 10field.private, signature { 5scalar.public, 3scalar.private }, true.public }";
        let value = Value::<P>::parse(expected).unwrap().1;
        assert_eq!(expected, value.to_string());
    }

    #[test]
    fn test_value_serialization() {
        // Test a value literal.
        let expected = Value::<P>::parse("10field.private").unwrap().1;
        let candidate = Value::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);

        // Test a value definition.
        let expected = Value::<P>::parse("message { 2group.public, 10field.private }").unwrap().1;
        let candidate = Value::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);

        // Test a value definition with a nested definition.
        let expected = Value::<P>::parse(
            "message { 2group.public, 10field.private, signature { 5scalar.public, 3scalar.private }, true.public }",
        )
        .unwrap()
        .1;
        let candidate = Value::from_bytes_le(&expected.to_bytes_le().unwrap()).unwrap();
        assert_eq!(expected, candidate);
    }

    #[test]
    fn test_parser_checks_num_depth() {
        // Create a value definition of max depth.
        let value = create_random_value_definition(<P as Program>::NUM_DEPTH);
        let value_string = value.to_string();
        assert!(Value::<P>::parse(&value_string).is_ok());

        // Create a value definition of max depth + 1.
        let value = create_random_value_definition(<P as Program>::NUM_DEPTH + 1);
        let value_string = value.to_string();
        assert!(Value::<P>::parse(&value_string).is_err());
    }

    #[test]
    fn test_write_le_checks_num_depth() {
        // Create a value definition of max depth.
        let value = create_random_value_definition(<P as Program>::NUM_DEPTH);
        assert!(value.write_le(Vec::new()).is_ok());

        // Create a value definition of max depth + 1.
        let value = create_random_value_definition(<P as Program>::NUM_DEPTH + 1);
        assert!(value.write_le(Vec::new()).is_err());
    }
}
