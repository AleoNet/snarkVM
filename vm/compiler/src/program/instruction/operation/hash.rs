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

use crate::{Opcode, Operand, Registers, Stack};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};

/// BHP256 is a collision-resistant hash function that processes inputs in 256-bit chunks.
pub type HashBHP256<N> = HashInstruction<N, { Hasher::BHP256 as u8 }>;
/// BHP512 is a collision-resistant hash function that processes inputs in 512-bit chunks.
pub type HashBHP512<N> = HashInstruction<N, { Hasher::BHP512 as u8 }>;
/// BHP768 is a collision-resistant hash function that processes inputs in 768-bit chunks.
pub type HashBHP768<N> = HashInstruction<N, { Hasher::BHP768 as u8 }>;
/// BHP1024 is a collision-resistant hash function that processes inputs in 1024-bit chunks.
pub type HashBHP1024<N> = HashInstruction<N, { Hasher::BHP1024 as u8 }>;

/// Pedersen64 is a collision-resistant hash function that processes inputs in 64-bit chunks.
pub type HashPED64<N> = HashInstruction<N, { Hasher::PED64 as u8 }>;
/// Pedersen128 is a collision-resistant hash function that processes inputs in 128-bit chunks.
pub type HashPED128<N> = HashInstruction<N, { Hasher::PED128 as u8 }>;

/// Poseidon2 is a cryptographic hash function that processes inputs in 2-field chunks.
pub type HashPSD2<N> = HashInstruction<N, { Hasher::PSD2 as u8 }>;
/// Poseidon4 is a cryptographic hash function that processes inputs in 4-field chunks.
pub type HashPSD4<N> = HashInstruction<N, { Hasher::PSD4 as u8 }>;
/// Poseidon8 is a cryptographic hash function that processes inputs in 8-field chunks.
pub type HashPSD8<N> = HashInstruction<N, { Hasher::PSD8 as u8 }>;

enum Hasher {
    BHP256,
    BHP512,
    BHP768,
    BHP1024,
    PED64,
    PED128,
    PSD2,
    PSD4,
    PSD8,
}

/// Hashes the operand into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct HashInstruction<N: Network, const VARIANT: u8> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network, const VARIANT: u8> HashInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Hash("hash.bhp256"),
            1 => Opcode::Hash("hash.bhp512"),
            2 => Opcode::Hash("hash.bhp768"),
            3 => Opcode::Hash("hash.bhp1024"),
            4 => Opcode::Hash("hash.ped64"),
            5 => Opcode::Hash("hash.ped128"),
            6 => Opcode::Hash("hash.psd2"),
            7 => Opcode::Hash("hash.psd4"),
            8 => Opcode::Hash("hash.psd8"),
            _ => panic!("Invalid hash instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly one input.
        debug_assert!(self.operands.len() == 1, "Hash operation must have one operand");
        // Return the operand.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, const VARIANT: u8> HashInstruction<N, VARIANT> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = registers.load(stack, &self.operands[0])?;
        // Hash the input.
        let output = match VARIANT {
            0 => N::hash_bhp256(&input.to_bits_le())?,
            1 => N::hash_bhp512(&input.to_bits_le())?,
            2 => N::hash_bhp768(&input.to_bits_le())?,
            3 => N::hash_bhp1024(&input.to_bits_le())?,
            4 => N::hash_ped64(&input.to_bits_le())?,
            5 => N::hash_ped128(&input.to_bits_le())?,
            6 => N::hash_psd2(&input.to_fields()?)?,
            7 => N::hash_psd4(&input.to_fields()?)?,
            8 => N::hash_psd8(&input.to_fields()?)?,
            _ => bail!("Invalid hash variant: {VARIANT}"),
        };
        // Convert the output to a stack value.
        let output = Value::Plaintext(Plaintext::Literal(Literal::Field(output), Default::default()));
        // Store the output.
        registers.store(stack, &self.destination, output)
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        use circuit::{ToBits, ToFields};

        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = registers.load_circuit(stack, &self.operands[0])?;
        // Hash the input.
        let output = match VARIANT {
            0 => A::hash_bhp256(&input.to_bits_le()),
            1 => A::hash_bhp512(&input.to_bits_le()),
            2 => A::hash_bhp768(&input.to_bits_le()),
            3 => A::hash_bhp1024(&input.to_bits_le()),
            4 => A::hash_ped64(&input.to_bits_le()),
            5 => A::hash_ped128(&input.to_bits_le()),
            6 => A::hash_psd2(&input.to_fields()),
            7 => A::hash_psd4(&input.to_fields()),
            8 => A::hash_psd8(&input.to_fields()),
            _ => bail!("Invalid hash variant: {VARIANT}"),
        };
        // Convert the output to a stack value.
        let output =
            circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Field(output), Default::default()));
        // Store the output.
        registers.store_circuit(stack, &self.destination, output)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, _stack: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 1 {
            bail!("Instruction '{}' expects 1 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        match VARIANT {
            0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => {
                Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field))])
            }
            _ => bail!("Invalid hash variant: {VARIANT}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Parser for HashInstruction<N, VARIANT> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the operand from the string.
        let (string, operand) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands: vec![operand], destination }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for HashInstruction<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for HashInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for HashInstruction<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            eprintln!("The number of operands must be 1, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        write!(f, "{} ", self.operands[0])?;
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for HashInstruction<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the operand.
        let operands = vec![Operand::read_le(&mut reader)?];
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the operation.
        Ok(Self { operands, destination })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for HashInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            return Err(error(format!("The number of operands must be 1, found {}", self.operands.len())));
        }
        // Write the operand.
        self.operands[0].write_le(&mut writer)?;
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
        let (string, hash) = HashBHP512::<CurrentNetwork>::parse("hash.bhp512 r0 into r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(hash.operands.len(), 1, "The number of operands is incorrect");
        assert_eq!(hash.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(hash.destination, Register::Locator(1), "The destination register is incorrect");
    }
}
