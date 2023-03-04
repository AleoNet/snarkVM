// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::{Opcode, Operand, Registers, Stack};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};

/// BHP256 is a collision-resistant function that processes inputs in 256-bit chunks.
pub type CommitBHP256<N> = CommitInstruction<N, { Committer::BHP256 as u8 }>;
/// BHP512 is a collision-resistant function that processes inputs in 512-bit chunks.
pub type CommitBHP512<N> = CommitInstruction<N, { Committer::BHP512 as u8 }>;
/// BHP768 is a collision-resistant function that processes inputs in 768-bit chunks.
pub type CommitBHP768<N> = CommitInstruction<N, { Committer::BHP768 as u8 }>;
/// BHP1024 is a collision-resistant function that processes inputs in 1024-bit chunks.
pub type CommitBHP1024<N> = CommitInstruction<N, { Committer::BHP1024 as u8 }>;

/// Pedersen64 is a collision-resistant function that processes inputs in 64-bit chunks.
pub type CommitPED64<N> = CommitInstruction<N, { Committer::PED64 as u8 }>;
/// Pedersen128 is a collision-resistant function that processes inputs in 128-bit chunks.
pub type CommitPED128<N> = CommitInstruction<N, { Committer::PED128 as u8 }>;

enum Committer {
    BHP256,
    BHP512,
    BHP768,
    BHP1024,
    PED64,
    PED128,
}

/// Commits the operand into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CommitInstruction<N: Network, const VARIANT: u8> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network, const VARIANT: u8> CommitInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Commit("commit.bhp256"),
            1 => Opcode::Commit("commit.bhp512"),
            2 => Opcode::Commit("commit.bhp768"),
            3 => Opcode::Commit("commit.bhp1024"),
            4 => Opcode::Commit("commit.ped64"),
            5 => Opcode::Commit("commit.ped128"),
            _ => panic!("Invalid 'commit' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly two inputs.
        debug_assert!(self.operands.len() == 2, "Commit operations must have two operands");
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, const VARIANT: u8> Parser for CommitInstruction<N, VARIANT> {
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
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands: vec![first, second], destination }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for CommitInstruction<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for CommitInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for CommitInstruction<N, VARIANT> {
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
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for CommitInstruction<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for CommitInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, commit) = CommitBHP512::<CurrentNetwork>::parse("commit.bhp512 r0 r1 into r2").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(commit.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(commit.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(commit.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(commit.destination, Register::Locator(2), "The destination register is incorrect");
    }
}
