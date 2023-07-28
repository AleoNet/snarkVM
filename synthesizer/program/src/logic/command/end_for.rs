// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use console::network::prelude::*;

/// A marker for the end of a for loop, e.g. `end.for;`.
/// Runs the body of the loop for each value in the range.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EndFor;

impl Parser for EndFor {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "end.for" keyword from the string.
        let (string, _) = tag("end.for")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self))
    }
}

impl FromStr for EndFor {
    type Err = Error;

    /// Parses a string into the command.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl Debug for EndFor {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for EndFor {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_internal(f, 0)
    }
}

impl EndFor {
    /// Prints the `EndFor` command with the given indentation depth.
    fn fmt_internal(&self, f: &mut Formatter, depth: usize) -> fmt::Result {
        /// The number of spaces to indent.
        const INDENT: usize = 2;

        write!(f, "{:indent$}end.for;", "", indent = depth * INDENT)
    }
}

impl FromBytes for EndFor {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut _reader: R) -> IoResult<Self> {
        Ok(Self)
    }
}

impl ToBytes for EndFor {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut _writer: W) -> IoResult<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let (string, _) = EndFor::parse("end.for;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
    }
}
