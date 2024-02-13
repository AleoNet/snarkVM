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
    traits::{RegistersLoad, RegistersLoadCircuit, RegistersStore, RegistersStoreCircuit, StackMatches, StackProgram},
    Opcode,
    Operand,
    MAX_ADDITIONAL_SEEDS,
};
use circuit::prelude::ToFields as CircuitToFields;
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, PlaintextType, Register, RegisterType, ToFields as ConsoleToFields},
    types::Boolean,
};
use core::fmt;
use std::{
    fmt::{Debug, Display, Formatter},
    io::{Read, Write},
    str::FromStr,
};

/// Returns true if the Varuna `proof` is valid for the given `vk`s and `input`s and stores the result into `destination`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VarunaVerify<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> VarunaVerify<N> {
    /// The maximum number of unique circuits that can be verified in a single Varuna proof.
    pub const MAX_UNIQUE_CIRCUITS: u8 = 32;

    /// Initializes a new `varuna.verify` instruction.
    #[inline]
    pub fn new(operands: Vec<Operand<N>>, destination: Register<N>) -> Result<Self> {
        // Sanity check the number of operands.
        ensure!(
            Self::is_valid_number_of_operands(operands.len()),
            "Instruction '{}' has the incorrect number of operands",
            Self::opcode()
        );
        // Return the instruction.
        Ok(Self { operands, destination })
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("varuna.verify")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check the number of operands.
        debug_assert!(
            Self::is_valid_number_of_operands(self.operands.len()),
            "Instruction '{}' has the incorrect number of operands",
            Self::opcode()
        );
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destination(&self) -> &Register<N> {
        &self.destination
    }

    /// Return whether the number of operands is valid.
    #[inline]
    pub fn is_valid_number_of_operands(num_operands: usize) -> bool {
        num_operands % 2 == 1 && num_operands <= 2 * Self::MAX_UNIQUE_CIRCUITS as usize + 1
    }
}

impl<N: Network> VarunaVerify<N> {
    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        todo!()
    }
}

impl<N: Network> Parser for VarunaVerify<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses an operand from the string.
        fn parse_operand<N: Network>(string: &str) -> ParserResult<Operand<N>> {
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the operand from the string.
            Operand::parse(string)
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the operands from the string.
        let (string, operands) = many1(parse_operand)(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" keyword from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        // Check the number of operands.
        match Self::is_valid_number_of_operands(operands.len()) {
            true => Ok((string, Self { operands, destination })),
            false => map_res(fail, |_: ParserResult<Self>| {
                Err(error("Failed to parse 'varuna.verify' opcode: incorrect number of operands"))
            })(string),
        }
    }
}

impl<N: Network> FromStr for VarunaVerify<N> {
    type Err = Error;

    /// Parses a string into an operation.
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

impl<N: Network> Debug for VarunaVerify<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for VarunaVerify<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Check that the number of operands is correct
        if !Self::is_valid_number_of_operands(self.operands.len()) {
            return Err(fmt::Error);
        }

        // Print the opcode.
        write!(f, "{} ", Self::opcode())?;
        // Print the operands.
        for operand in &self.operands {
            write!(f, "{} ", operand)?;
        }
        // Print the destination register.
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network> FromBytes for VarunaVerify<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of operands.
        let num_operands = u8::read_le(&mut reader)? as usize;

        // Ensure that the number of operands is correct.
        if !Self::is_valid_number_of_operands(num_operands) {
            return Err(error("The number of operands is incorrect"));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(num_operands);
        // Read the operands.
        for _ in 0..num_operands {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Return the command.
        Ok(Self { operands, destination })
    }
}

impl<N: Network> ToBytes for VarunaVerify<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure that the number of operands is correct.
        if Self::is_valid_number_of_operands(self.operands().len()) {
            return Err(error("The number of operands must be odd"));
        }

        // Write the number of operands.
        u8::try_from(self.operands.len()).or_halt::<N>().write_le(&mut writer)?;

        // Write the operands.
        for operand in &self.operands {
            operand.write_le(&mut writer)?;
        }

        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_parse() {
        let (string, varuna_verify) = VarunaVerify::<CurrentNetwork>::parse("varuna.verify r0 r1 r2 into r3").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(varuna_verify.operands.len(), 3, "The number of operands is incorrect");
        assert_eq!(
            varuna_verify.operands[0],
            Operand::Register(Register::Locator(0)),
            "The first operand is incorrect"
        );
        assert_eq!(
            varuna_verify.operands[1],
            Operand::Register(Register::Locator(1)),
            "The second operand is incorrect"
        );
        assert_eq!(
            varuna_verify.operands[2],
            Operand::Register(Register::Locator(2)),
            "The third operand is incorrect"
        );
        assert_eq!(varuna_verify.destination, Register::Locator(3), "The destination register is incorrect");
    }
}
