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

use crate::{Annotation, Identifier, Program, Sanitizer};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use std::io::{Read, Result as IoResult, Write};

/// An member statement defines a name for an annotation, and is of the form
/// `{identifier} as {annotation};`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Member<P: Program> {
    /// The name of the member.
    name: Identifier<P>,
    /// The annotation of the member.
    // TODO: If composites are not allowed to be nested, then this should be changed `LiteralType`.
    //  Using `Annotation` implies that a `Member` can be a composite type and thus we can have
    //  r0.<id1>.<id2>.
    annotation: Annotation<P>,
}

impl<P: Program> Member<P> {
    /// Returns the name of the member.
    #[inline]
    pub fn name(&self) -> &Identifier<P> {
        &self.name
    }

    /// Returns the annotation of the member.
    #[inline]
    pub fn annotation(&self) -> &Annotation<P> {
        &self.annotation
    }
}

impl<P: Program> Parser for Member<P> {
    type Environment = P::Environment;

    /// Parses a string into an member.
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the name from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the " as " from the string.
        let (string, _) = tag(" as ")(string)?;
        // Parse the annotation from the string.
        let (string, annotation) = Annotation::parse(string)?;
        // Parse the semicolon ';' keyword from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { name, annotation }))
    }
}

impl<P: Program> fmt::Display for Member<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{name} as {annotation};", name = self.name, annotation = self.annotation)
    }
}

impl<P: Program> FromBytes for Member<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let name = FromBytes::read_le(&mut reader)?;
        let annotation = FromBytes::read_le(&mut reader)?;
        Ok(Self { name, annotation })
    }
}

impl<P: Program> ToBytes for Member<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.name.write_le(&mut writer)?;
        self.annotation.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Process;

    type P = Process;

    #[test]
    fn test_member_parse() {
        let member_string = "owner as address.public;";
        let member = Member::<P>::parse(member_string).unwrap().1;
        assert_eq!(member.name(), &Identifier::from_str("owner"));
        assert_eq!(member.annotation(), &Annotation::from_str("address.public"));
    }

    #[test]
    fn test_member_display() {
        let member_string = "owner as address.public;";
        let member = Member::<P>::parse(member_string).unwrap().1;
        assert_eq!(member_string, format!("{member}"));
    }
}
