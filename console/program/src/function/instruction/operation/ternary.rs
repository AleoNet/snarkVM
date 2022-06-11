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

use crate::{
    function::instruction::{Operand, Operation},
    Plaintext,
    Register,
    Registers,
};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use core::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Ternary<N: Network, O: Operation> {
    /// The first operand.
    first: Operand<N>,
    /// The second operand.
    second: Operand<N>,
    /// The third operand.
    third: Operand<N>,
    /// The destination register.
    destination: Register<N>,
    /// PhantomData.
    _phantom: PhantomData<O>,
}

impl<N: Network, O: Operation<Inputs = (Plaintext<N>, Plaintext<N>, Plaintext<N>), Output = Plaintext<N>>>
    Ternary<N, O>
{
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(&self, registers: &mut Registers<N>) -> Result<()> {
        // Load the first, second, and third operands.
        let first = registers.load(&self.first)?;
        let second = registers.load(&self.second)?;
        let third = registers.load(&self.third)?;
        // Evaluate the operation and store the output.
        registers.store(&self.destination, O::evaluate((first, second, third))?)
    }
}

impl<N: Network, O: Operation> Parser for Ternary<N, O> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(O::OPCODE)(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the third operand from the string.
        let (string, third) = Operand::parse(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" into ")(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { first, second, third, destination, _phantom: PhantomData }))
    }
}

impl<N: Network, O: Operation> FromStr for Ternary<N, O> {
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

impl<N: Network, O: Operation> Debug for Ternary<N, O> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, O: Operation> Display for Ternary<N, O> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} {} {} {} into {}", O::OPCODE, self.first, self.second, self.third, self.destination)
    }
}

impl<N: Network, O: Operation> FromBytes for Ternary<N, O> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let first = Operand::read_le(&mut reader)?;
        let second = Operand::read_le(&mut reader)?;
        let third = Operand::read_le(&mut reader)?;
        let destination = Register::read_le(&mut reader)?;
        Ok(Self { first, second, third, destination, _phantom: PhantomData })
    }
}

impl<N: Network, O: Operation> ToBytes for Ternary<N, O> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.first.write_le(&mut writer)?;
        self.second.write_le(&mut writer)?;
        self.third.write_le(&mut writer)?;
        self.destination.write_le(&mut writer)
    }
}
