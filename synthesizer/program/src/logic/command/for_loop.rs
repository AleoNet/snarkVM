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

use crate::{
    traits::{FinalizeStoreTrait, RegistersLoad, RegistersStore, StackMatches, StackProgram},
    Command,
    FinalizeRegistersState,
    Opcode,
    Operand,
};
use console::{
    network::prelude::*,
    program::{Field, Literal, Register, Scalar, Value, I128, I16, I32, I64, I8, U128, U16, U32, U64, U8},
};

/// A for loop, e.g. `for r0 in 0u8..255u8: ... end.for;`.
/// Runs the body of the loop for each value in the range.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ForLoop<N: Network> {
    /// The loop register.
    register: Register<N>,
    /// The loop range.
    range: Range<N>,
    /// The loop body.
    body: Vec<Command<N>>,
}

impl<N: Network> ForLoop<N> {
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

    /// Returns the loop body.
    #[inline]
    pub fn body(&self) -> &[Command<N>] {
        &self.body
    }
}

impl<N: Network> ForLoop<N> {
    /// Finalizes the command.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        store: &impl FinalizeStoreTrait<N>,
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N> + FinalizeRegistersState<N>),
    ) -> Result<()> {
        // Get the start of the range.
        let start = registers.load_literal(stack, self.range.start())?;
        // Get the end of the range.
        let end = registers.load_literal(stack, self.range.end())?;
        // Get the direction of the range.
        let is_increasing = match (&start, &end) {
            (Literal::Field(start), Literal::Field(end)) => start <= end,
            (Literal::Scalar(start), Literal::Scalar(end)) => start <= end,
            (Literal::I8(start), Literal::I8(end)) => start <= end,
            (Literal::I16(start), Literal::I16(end)) => start <= end,
            (Literal::I32(start), Literal::I32(end)) => start <= end,
            (Literal::I64(start), Literal::I64(end)) => start <= end,
            (Literal::I128(start), Literal::I128(end)) => start <= end,
            (Literal::U8(start), Literal::U8(end)) => start <= end,
            (Literal::U16(start), Literal::U16(end)) => start <= end,
            (Literal::U32(start), Literal::U32(end)) => start <= end,
            (Literal::U64(start), Literal::U64(end)) => start <= end,
            (Literal::U128(start), Literal::U128(end)) => start <= end,
            _ => bail!("Invalid range."),
        };
        // Store the start of the range in the register.
        registers.store(stack, self.register(), Value::from(start))?;
        // If the value of the register is within the range, run the loop body.
        let value = registers.load_literal(stack, &Operand::Register(self.register().clone()))?;
        while match (&value, &end) {
            (Literal::Field(value), Literal::Field(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::Scalar(value), Literal::Scalar(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::I8(value), Literal::I8(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::I16(value), Literal::I16(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::I32(value), Literal::I32(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::I64(value), Literal::I64(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::I128(value), Literal::I128(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::U8(value), Literal::U8(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::U16(value), Literal::U16(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::U32(value), Literal::U32(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::U64(value), Literal::U64(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            (Literal::U128(value), Literal::U128(end)) => {
                if is_increasing {
                    value <= end
                } else {
                    value >= end
                }
            }
            _ => bail!("Invalid register and ending range."),
        } {
            // Run the loop body.
            for command in &self.body {
                command.finalize(stack, store, registers)?;
            }
            // Increment or decrement the register depending on the direction of the loop.
            match &value {
                Literal::Field(value) => {
                    if is_increasing {
                        registers.store(
                            stack,
                            self.register(),
                            Value::from(Literal::Field(value.add(Field::one()))),
                        )?;
                    } else {
                        registers.store(
                            stack,
                            self.register(),
                            Value::from(Literal::Field(value.sub(Field::one()))),
                        )?;
                    }
                }
                Literal::Scalar(value) => {
                    if is_increasing {
                        registers.store(
                            stack,
                            self.register(),
                            Value::from(Literal::Scalar(value.add(Scalar::one()))),
                        )?;
                    } else {
                        registers.store(
                            stack,
                            self.register(),
                            Value::from(Literal::Scalar(value.sub(Scalar::one()))),
                        )?;
                    }
                }
                Literal::I8(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::I8(value.add(I8::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::I8(value.sub(I8::one()))))?;
                    }
                }
                Literal::I16(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::I16(value.add(I16::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::I16(value.sub(I16::one()))))?;
                    }
                }
                Literal::I32(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::I32(value.add(I32::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::I32(value.sub(I32::one()))))?;
                    }
                }
                Literal::I64(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::I64(value.add(I64::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::I64(value.sub(I64::one()))))?;
                    }
                }
                Literal::I128(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::I128(value.add(I128::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::I128(value.sub(I128::one()))))?;
                    }
                }
                Literal::U8(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::U8(value.add(U8::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::U8(value.sub(U8::one()))))?;
                    }
                }
                Literal::U16(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::U16(value.add(U16::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::U16(value.sub(U16::one()))))?;
                    }
                }
                Literal::U32(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::U32(value.add(U32::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::U32(value.sub(U32::one()))))?;
                    }
                }
                Literal::U64(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::U64(value.add(U64::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::U64(value.sub(U64::one()))))?;
                    }
                }
                Literal::U128(value) => {
                    if is_increasing {
                        registers.store(stack, self.register(), Value::from(Literal::U128(value.add(U128::one()))))?;
                    } else {
                        registers.store(stack, self.register(), Value::from(Literal::U128(value.sub(U128::one()))))?;
                    }
                }
                _ => bail!("Invalid register value."),
            }
        }
        Ok(())
    }
}

impl<N: Network> Parser for ForLoop<N> {
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
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the ":" from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the loop body from the string.
        let (string, body) = many1(terminated(Command::parse, Sanitizer::parse_whitespaces))(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the "end.for" keyword from the string.
        let (string, _) = tag("end.for")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { register, range, body }))
    }
}

impl<N: Network> FromStr for ForLoop<N> {
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

impl<N: Network> Debug for ForLoop<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ForLoop<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_internal(f, 0)
    }
}

impl<N: Network> ForLoop<N> {
    /// Prints the plaintext with the given indentation depth.
    fn fmt_internal(&self, f: &mut Formatter, depth: usize) -> fmt::Result {
        /// The number of spaces to indent.
        const INDENT: usize = 2;

        // Print the loop header.
        write!(f, "{:indent$}for {} in {}:", "", self.register, self.range, indent = depth * INDENT)?;
        // Print the loop body.
        for command in &self.body {
            // Print the command.
            match command {
                // TODO: Enable this once the for loop command is implemented.
                // Command::ForLoop(command) => {
                //     // Print the command.
                //     command.fmt_internal(f, depth + 1)?;
                // }
                _ => {
                    // Print the command.
                    write!(f, "{:indent$}{}", "", command, indent = (depth + 1) * INDENT)?;
                }
            }
        }
        // Print the loop footer.
        write!(f, "{:indent$}end.for;", "", indent = depth * INDENT)
    }
}

impl<N: Network> FromBytes for ForLoop<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the register.
        let register = Register::read_le(&mut reader)?;
        // Read the range.
        let range = Range::read_le(&mut reader)?;
        // Read the number of commands in the loop body.
        let num_commands = u16::read_le(&mut reader)?;
        // Read the commands in the loop body.
        let mut body = Vec::with_capacity(num_commands as usize);
        for _ in 0..num_commands {
            body.push(Command::read_le(&mut reader)?);
        }
        // Return the for loop.
        Ok(Self { register, range, body })
    }
}

impl<N: Network> ToBytes for ForLoop<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the register.
        self.register.write_le(&mut writer)?;
        // Write the range.
        self.range.write_le(&mut writer)?;
        // Write the number of commands in the loop body.
        u16::try_from(self.body.len())
            .or_halt_with::<N>("The loop body exceeds u16::MAX commands")
            .write_le(&mut writer)?;
        // Write the commands in the loop body.
        for command in &self.body {
            command.write_le(&mut writer)?;
        }
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
    use console::{network::Testnet3, program::Register, types::U8};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, for_loop) =
            ForLoop::<CurrentNetwork>::parse("for r0 in 0u8..7u8: add r0 r0 into r1; end.for;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(for_loop.register, Register::Locator(0));
        assert_eq!(for_loop.range, Range {
            start: Operand::Literal(Literal::U8(U8::new(0))),
            end: Operand::Literal(Literal::U8(U8::new(7))),
        });
        assert_eq!(for_loop.range.start(), &Operand::Literal(Literal::U8(U8::new(0))));
        assert_eq!(for_loop.range.end(), &Operand::Literal(Literal::U8(U8::new(7))));
        assert_eq!(for_loop.body.len(), 1);
        assert_eq!(for_loop.body[0], Command::from_str("add r0 r0 into r1;").unwrap());
    }
}
