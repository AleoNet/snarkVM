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

mod member;

use crate::{definition::member::Member, Annotation, Identifier, Program, Sanitizer, Value};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{error, has_duplicates, FromBytes, ToBytes};

use core::fmt;
use std::io::{Read, Result as IoResult, Write};

/// A definition is a custom type or record type that represents a collection of circuits.
/// A definition does not have a mode; rather its individual members are annotated with modes.
/// A definition is defined by an identifier (such as `message`) and a list of members,
/// such as `[(sender, address.public), (amount, i64.private)]`, where the left entry is an identifier,
/// and the right entry is a type annotation.
///
/// A register member format is used to access individual members of a definition. For example,
/// if the `record` definition is assigned to register `r0`, individual members can be accessed
/// as `r0.owner` or `r0.value`. This generalizes to the format, i.e. `r{locator}.{member}`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Definition<P: Program> {
    /// A custom struct consists of its name and a list of members.
    Struct(Identifier<P>, Vec<Member<P>>),
    /// A record type consists of its name and a list of members.
    Record(Identifier<P>, Vec<Member<P>>),
}

impl<P: Program> Definition<P> {
    /// Returns the name of the definition.
    #[inline]
    pub fn name(&self) -> &Identifier<P> {
        match self {
            Self::Struct(name, _) => name,
            Self::Record(name, _) => name,
        }
    }

    /// Returns the members of the definition.
    #[inline]
    pub fn members(&self) -> &[Member<P>] {
        match self {
            Self::Struct(_, members) => members,
            Self::Record(_, members) => members,
        }
    }

    /// Returns `true` if the definition matches the format of the given value.
    /// This method starts by checking that the top-level members match, then recursively checks
    /// that all nested definitions match as well.
    #[inline]
    pub fn matches(&self, value: &Value<P>) -> bool {
        match value {
            Value::Literal(..) => false,
            Value::Definition(name, values) => {
                name == self.name()
                    && values.len() == self.members().len()
                    && values
                        .iter()
                        .zip_eq(self.members().iter())
                        // Members in the value are literals.
                        .all(|(value, member)| match value.annotation() {
                            // If the annotation is a literal, ensure the literal type matches the member type.
                            Annotation::Literal(literal_type) => &Annotation::Literal(literal_type) == member.annotation(),
                            // If the annotation is a definition, ensure the member value matches the definition.
                            Annotation::Definition(definition_name) => {
                                // Retrieve the definition from the program.
                                match P::get_definition(&definition_name) {
                                    // Ensure the value matches its expected definition.
                                    Some(definition) => definition.matches(value),
                                    None => false,
                                }
                            }
                        })
            }
        }
    }
}

impl<P: Program> Parser for Definition<P> {
    type Environment = P::Environment;

    /// Parses a string into a definition.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;

        alt((
            |string| {
                // Parse the keyword and space from the string.
                let (string, _) = tag("struct ")(string)?;
                // Parse the struct name from the string.
                let (string, name) = Identifier::parse(string)?;
                // Parse the colon ':' keyword from the string.
                let (string, _) = tag(":")(string)?;
                // Parse the members from the string.
                let (string, members) = many1(Member::parse)(string)?;
                // Ensure the members has no duplicate names.
                if has_duplicates(members.iter().map(|member| member.name())) {
                    P::halt(format!("Duplicate member names in struct '{}'", name))
                }
                // Ensure the number of members is within `P::NUM_DEPTH`.
                if members.len() > P::NUM_DEPTH {
                    P::halt("Failed to serialize struct: too many members")
                }

                Ok((string, Self::Struct(name, members)))
            },
            |string| {
                // Parse the keyword and space from the string.
                let (string, _) = tag("record ")(string)?;
                // Parse the type name from the string.
                let (string, name) = Identifier::parse(string)?;
                // Parse the colon ':' keyword from the string.
                let (string, _) = tag(":")(string)?;
                // Parse the members from the string.
                let (string, members) = many1(Member::parse)(string)?;
                // Ensure the members has no duplicate names.
                if has_duplicates(members.iter().map(|member| member.name())) {
                    P::halt(format!("Duplicate member names in record '{}'", name))
                }
                // Ensure the number of members is within `P::NUM_DEPTH`.
                if members.len() > P::NUM_DEPTH {
                    P::halt("Failed to serialize record: too many members")
                }

                Ok((string, Self::Record(name, members)))
            },
        ))(string)
    }
}

#[allow(clippy::format_push_string)]
impl<P: Program> fmt::Display for Definition<P> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (type_name, name, members) = match self {
            Self::Struct(name, members) => ("struct", name, members),
            Self::Record(name, members) => ("record", name, members),
        };

        let mut output = format!("{} {}:\n", type_name, name);
        for member in members {
            output += &format!("    {member}\n");
        }
        output.pop(); // trailing newline
        write!(f, "{}", output)
    }
}

impl<P: Program> FromBytes for Definition<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Read the name.
        let name = Identifier::read_le(&mut reader)?;
        // Read the members.
        let num_members = u8::read_le(&mut reader)?;
        let mut members = Vec::with_capacity(num_members as usize);
        for _ in 0..num_members {
            members.push(Member::read_le(&mut reader)?);
        }
        // Ensure the members has no duplicate names.
        if has_duplicates(members.iter().map(|member| member.name())) {
            return Err(error(format!("Duplicate member names in definition '{}'", name)));
        }
        match variant {
            0 => Ok(Self::Struct(name, members)),
            1 => Ok(Self::Record(name, members)),
            2.. => Err(error(format!("Failed to deserialize definition variant {variant}"))),
        }
    }
}

impl<P: Program> ToBytes for Definition<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Struct(name, members) => {
                u8::write_le(&0u8, &mut writer)?;
                name.write_le(&mut writer)?;
                (members.len() as u16).write_le(&mut writer)?;
                members.write_le(&mut writer)
            }
            Self::Record(name, members) => {
                // Ensure the members has no duplicate names.
                if has_duplicates(members.iter().map(|member| member.name())) {
                    return Err(error(format!("Duplicate member names in definition '{}'", name)));
                }
                // Ensure the number of members is within `P::NUM_DEPTH`.
                if members.len() > P::NUM_DEPTH {
                    return Err(error("Failed to serialize definition: too many members"));
                }

                u8::write_le(&1u8, &mut writer)?;
                name.write_le(&mut writer)?;
                (members.len() as u8).write_le(&mut writer)?;
                members.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Annotation, Process};

    type P = Process;

    #[test]
    fn test_definition_parse() {
        let message = Definition::<P>::parse(
            r"
struct message:
    sender as address.public;
    amount as i64.private;
",
        )
        .unwrap()
        .1;
        assert_eq!(message.name(), &Identifier::from_str("message"));
        assert_eq!(message.members().len(), 2);
        assert_eq!(message.members()[0].name(), &Identifier::from_str("sender"));
        assert_eq!(message.members()[0].annotation(), &Annotation::from_str("address.public"));
        assert_eq!(message.members()[1].name(), &Identifier::from_str("amount"));
        assert_eq!(message.members()[1].annotation(), &Annotation::from_str("i64.private"));

        let token = Definition::<P>::parse(
            r"
record token:
    owner as address.public;
    amount as i64.private;
",
        )
        .unwrap()
        .1;
        assert_eq!(token.name(), &Identifier::from_str("token"));
        assert_eq!(token.members().len(), 2);
        assert_eq!(token.members()[0].name(), &Identifier::from_str("owner"));
        assert_eq!(token.members()[0].annotation(), &Annotation::from_str("address.public"));
        assert_eq!(token.members()[1].name(), &Identifier::from_str("amount"));
        assert_eq!(token.members()[1].annotation(), &Annotation::from_str("i64.private"));
    }

    #[test]
    fn test_definition_display() {
        let expected = "struct message:\n    sender as address.public;\n    amount as i64.private;";
        let message = Definition::<P>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{}", message));

        let expected = "record token:\n    owner as address.public;\n    amount as i64.private;";
        let token = Definition::<P>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{}", token));
    }
}
