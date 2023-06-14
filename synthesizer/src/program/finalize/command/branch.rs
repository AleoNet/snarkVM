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
use console::{network::prelude::*, program::Identifier};

/// Jumps to `position`, if `first` equals `second`.
pub type BranchEq<N> = Branch<N, { Variant::BranchEq as u8 }>;
/// Jumps to `position`, if `first` does **not** equal `second`.
pub type BranchNeq<N> = Branch<N, { Variant::BranchNeq as u8 }>;

enum Variant {
    BranchEq,
    BranchNeq,
}

/// Compares `first` and `second` and jumps to `position`, if the condition is met.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Branch<N: Network, const VARIANT: u8> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The position.
    position: Identifier<N>,
}

impl<N: Network, const VARIANT: u8> Branch<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Command("branch.eq"),
            1 => Opcode::Command("branch.neq"),
            _ => panic!("Invalid 'branch' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that there are exactly two operands.
        debug_assert!(self.operands.len() == 2, "Instruction '{}' must have two operands", Self::opcode());
        // Return the operands.
        &self.operands
    }

    /// Returns the position.
    #[inline]
    pub fn position(&self) -> &Identifier<N> {
        &self.position
    }
}

impl<N: Network, const VARIANT: u8> Parser for Branch<N, VARIANT> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "to" from the string.
        let (string, _) = tag("to")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the position from the string.
        let (string, position) = Identifier::parse(string)?;

        Ok((string, Self { operands: vec![first, second], position }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for Branch<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for Branch<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for Branch<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            eprintln!("The number of operands must be 2, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "to {}", self.position)
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for Branch<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }
        // Read the position.
        let position = Identifier::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, position })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for Branch<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the position.
        self.position.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use console::{
        network::Testnet3,
        program::{Identifier, Register},
    };

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, branch) = BranchEq::<CurrentNetwork>::parse("branch.eq r0 r1 to exit").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(branch.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(branch.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(branch.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(branch.position, Identifier::from_str("exit").unwrap(), "The position is incorrect");

        let (string, branch) = BranchNeq::<CurrentNetwork>::parse("branch.neq r3 r4 to start").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(branch.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(branch.operands[0], Operand::Register(Register::Locator(3)), "The first operand is incorrect");
        assert_eq!(branch.operands[1], Operand::Register(Register::Locator(4)), "The second operand is incorrect");
        assert_eq!(branch.position, Identifier::from_str("start").unwrap(), "The position is incorrect");
    }
}
