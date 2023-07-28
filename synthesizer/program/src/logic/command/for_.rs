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

use crate::{Opcode, Operand};
use console::{network::prelude::*, program::Register};

/// The loop header, e.g. `for r0 in 0u8..255u8:`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct For<N: Network> {
    /// The loop register.
    register: Register<N>,
    /// The loop range.
    range: Range<N>,
}

impl<N: Network> For<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("for")
    }

    /// Returns the register.
    #[inline]
    pub const fn register(&self) -> &Register<N> {
        &self.register
    }

    /// Returns the range.
    #[inline]
    pub const fn range(&self) -> &Range<N> {
        &self.range
    }
}

impl<N: Network> Parser for For<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the register from the string.
        let (string, register) = Register::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the "in" keyword from the string.
        let (string, _) = tag("in")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the range from the string.
        let (string, range) = Range::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse(string)?;

        // Parse the ":" from the string.
        let (string, _) = tag(":")(string)?;

        Ok((string, Self { register, range }))
    }
}

impl<N: Network> FromStr for For<N> {
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

impl<N: Network> Debug for For<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for For<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_internal(f, 0)
    }
}

impl<N: Network> For<N> {
    /// Prints the `For` command with the given indentation depth.
    fn fmt_internal(&self, f: &mut Formatter, depth: usize) -> fmt::Result {
        /// The number of spaces to indent.
        const INDENT: usize = 2;

        write!(f, "{:indent$}for {} in {}:", "", self.register, self.range, indent = depth * INDENT)
    }
}

impl<N: Network> FromBytes for For<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the register.
        let register = Register::read_le(&mut reader)?;
        // Read the range.
        let range = Range::read_le(&mut reader)?;
        // Return the loop header.
        Ok(Self { register, range })
    }
}

impl<N: Network> ToBytes for For<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the register.
        self.register.write_le(&mut writer)?;
        // Write the range.
        self.range.write_le(&mut writer)?;
        Ok(())
    }
}

/// A loop range.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Range<N: Network> {
    /// The start of the range.
    start: Operand<N>,
    /// The end of the range.
    end: Operand<N>,
}

impl<N: Network> Range<N> {
    /// Gets the start of the range.
    #[inline]
    pub fn start(&self) -> &Operand<N> {
        &self.start
    }

    /// Gets the end of the range.
    #[inline]
    pub fn end(&self) -> &Operand<N> {
        &self.end
    }
}

impl<N: Network> Parser for Range<N> {
    /// Parses a string into a `Range`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the start of the range from the string.
        let (string, start) = Operand::parse(string)?;
        // Parse the ".." from the string.
        let (string, _) = tag("..")(string)?;
        // Parse the end of the range from the string.
        let (string, end) = Operand::parse(string)?;
        // Return the range.
        Ok((string, Self { start, end }))
    }
}

impl<N: Network> FromStr for Range<N> {
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

impl<N: Network> Debug for Range<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Range<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Print the range.
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl<N: Network> FromBytes for Range<N> {
    /// Reads a `Range` from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the start of the range.
        let start = Operand::read_le(&mut reader)?;
        // Read the end of the range.
        let end = Operand::read_le(&mut reader)?;
        // Return the range.
        Ok(Self { start, end })
    }
}

impl<N: Network> ToBytes for Range<N> {
    /// Writes the range to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the start of the range.
        self.start.write_le(&mut writer)?;
        // Write the end of the range.
        self.end.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{
        network::Testnet3,
        program::{Literal, Register},
        types::U8,
    };

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, for_) = For::<CurrentNetwork>::parse("for r0 in 0u8..7u8:").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(for_.register, Register::Locator(0));
        assert_eq!(for_.range, Range {
            start: Operand::Literal(Literal::U8(U8::new(0))),
            end: Operand::Literal(Literal::U8(U8::new(7))),
        });
        assert_eq!(for_.range.start(), &Operand::Literal(Literal::U8(U8::new(0))));
        assert_eq!(for_.range.end(), &Operand::Literal(Literal::U8(U8::new(7))));
    }
}
