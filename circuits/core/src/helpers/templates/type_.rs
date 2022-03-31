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

use crate::{Annotation, Identifier, Sanitizer};
use snarkvm_circuits_types::prelude::*;

use core::fmt;

/// A custom type represents a collection of circuit members.
/// A custom type does not have a mode; rather its individual members are annotated with modes.
/// A custom type is defined by an name (such as `message`) and a list of members,
/// such as `[(sender, address.public), (amount, i64.private)]`, where the left entry is an identifier,
/// and the right entry is a type annotation.
///
/// A register member format is used to access individual members of a custom type. For example,
/// if the `record` template is assigned to register `r0`, individual members can be accessed
/// as `r0.owner` or `r0.value`. This generalizes to the format, i.e. `r{locator}.{member}`.
#[derive(Clone, Debug)]
pub struct Type<E: Environment> {
    /// The name of the type.
    name: Identifier<E>,
    /// The members of the type.
    members: Vec<(Identifier<E>, Annotation<E>)>,
}

impl<E: Environment> Type<E> {
    /// Initializes a new type.
    pub fn new(name: Identifier<E>, members: Vec<(Identifier<E>, Annotation<E>)>) -> Self {
        Self { name, members }
    }

    /// Returns the name of the type.
    #[inline]
    pub fn name(&self) -> &Identifier<E> {
        &self.name
    }

    /// Returns the members of the type.
    #[inline]
    pub fn members(&self) -> &[(Identifier<E>, Annotation<E>)] {
        &self.members
    }
}

impl<E: Environment> TypeName for Type<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "type"
    }
}

impl<E: Environment> Parser for Type<E> {
    type Environment = E;

    /// Parses a string into a type.
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'type' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the type name from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the members from the string.
        let (string, members) = many1(|s| {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(s)?;
            // Parse the member name from the string.
            let (string, identifier) = Identifier::parse(string)?;
            // Parse the " as " from the string.
            let (string, _) = tag(" as ")(string)?;
            // Parse the member type from the string.
            let (string, annotation) = Annotation::parse(string)?;
            // Parse the semicolon ';' keyword from the string.
            let (string, _) = tag(";")(string)?;

            Ok((string, (identifier, annotation)))
        })(string)?;

        Ok((string, Self::new(name, members)))
    }
}

impl<E: Environment> fmt::Display for Type<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = format!("{} {}:\n", Self::type_name(), self.name);
        for (identifier, annotation) in &self.members {
            output += &format!("    {identifier} as {annotation};\n");
        }
        output.pop(); // trailing newline
        write!(f, "{}", output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::environment::Circuit;

    type E = Circuit;

    #[test]
    fn test_type_parse() {
        let type_string = "type message: sender as address.public; amount as i64.private;";
        let message = Type::<E>::parse(type_string).unwrap().1;
        assert_eq!(message.name(), &Identifier::from_str("message"));
        assert_eq!(message.members().len(), 2);
        assert_eq!(message.members()[0].0, Identifier::from_str("sender"));
        assert_eq!(message.members()[0].1, Annotation::from_str("address.public"));
        assert_eq!(message.members()[1].0, Identifier::from_str("amount"));
        assert_eq!(message.members()[1].1, Annotation::from_str("i64.private"));
    }

    #[test]
    fn test_type_display() {
        let type_string = "type message:\n    sender as address.public;\n    amount as i64.private;";
        let message = Type::<E>::parse(type_string).unwrap().1;
        assert_eq!(type_string, format!("{}", message));
    }
}
