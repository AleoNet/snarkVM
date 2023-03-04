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

use crate::{Opcode, Operand, Operation};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, PlaintextType, Register, RegisterType},
};

use core::marker::PhantomData;

/// A unary literal operation.
pub type UnaryLiteral<N, O> = Literals<N, O, 1>;
/// A binary literal operation.
pub type BinaryLiteral<N, O> = Literals<N, O, 2>;
/// A ternary literal operation.
pub type TernaryLiteral<N, O> = Literals<N, O, 3>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Literals<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// PhantomData.
    _phantom: PhantomData<O>,
}

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize>
    Literals<N, O, NUM_OPERANDS>
{
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        O::OPCODE
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> Parser
    for Literals<N, O, NUM_OPERANDS>
{
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*O::OPCODE)(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            N::halt(format!("The number of operands must be <= {}", N::MAX_OPERANDS))
        }

        // Initialize a vector to store the operands.
        let mut operands = Vec::with_capacity(NUM_OPERANDS);
        // Initialize a tracker for the string.
        let mut string_tracker = string;
        // Parse the operands from the string.
        for _ in 0..NUM_OPERANDS {
            // Parse the operand from the string.
            let (string, operand) = Operand::parse(string_tracker)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Add the operand to the vector.
            operands.push(operand);
            // Update the string tracker.
            string_tracker = string;
        }
        // Set the string to the tracker.
        let string = string_tracker;

        // Parse the "into " from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands, destination, _phantom: PhantomData }))
    }
}

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> FromStr
    for Literals<N, O, NUM_OPERANDS>
{
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

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> Debug
    for Literals<N, O, NUM_OPERANDS>
{
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> Display
    for Literals<N, O, NUM_OPERANDS>
{
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            eprintln!("The number of operands must be <= {}", N::MAX_OPERANDS);
            return Err(fmt::Error);
        }
        // Ensure the number of operands is correct.
        if self.operands.len() > NUM_OPERANDS {
            eprintln!("The number of operands must be {NUM_OPERANDS}");
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", O::OPCODE)?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> FromBytes
    for Literals<N, O, NUM_OPERANDS>
{
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be <= {}", N::MAX_OPERANDS)));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(NUM_OPERANDS);
        // Read the operands.
        for _ in 0..NUM_OPERANDS {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the operation.
        Ok(Self { operands, destination, _phantom: PhantomData })
    }
}

impl<N: Network, O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize> ToBytes
    for Literals<N, O, NUM_OPERANDS>
{
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be <= {}", N::MAX_OPERANDS)));
        }
        // Ensure the number of operands is correct.
        if self.operands.len() > NUM_OPERANDS {
            return Err(error(format!("The number of operands must be {NUM_OPERANDS}")));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}
