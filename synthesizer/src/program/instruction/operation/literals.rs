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

use crate::{Opcode, Operand, Operation, Registers, Stack};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, PlaintextType, Register, RegisterType},
};

use core::marker::PhantomData;

/// A unary literal operation.
pub type UnaryLiteral<N, O, const NUM_DESTINATIONS: usize> = Literals<N, O, 1, NUM_DESTINATIONS>;
/// A binary literal operation.
pub type BinaryLiteral<N, O, const NUM_DESTINATIONS: usize> = Literals<N, O, 2, NUM_DESTINATIONS>;
/// A ternary literal operation.
pub type TernaryLiteral<N, O, const NUM_DESTINATIONS: usize> = Literals<N, O, 3, NUM_DESTINATIONS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Literals<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destinations: Vec<Register<N>>,
    /// PhantomData.
    _phantom: PhantomData<O>,
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
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
        self.destinations.clone()
    }
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
{
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands", O::OPCODE, self.operands.len())
        }
        // Ensure the number of destinations is correct.
        if self.destinations.len() != NUM_DESTINATIONS {
            bail!(
                "Instruction '{}' expects {NUM_DESTINATIONS} destinations, found {} destinations",
                O::OPCODE,
                self.destinations.len()
            )
        }

        // Load the operands literals.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_literal(stack, operand)).try_collect()?;
        // Compute the operands register types.
        let input_types: Vec<_> =
            inputs.iter().map(|input| RegisterType::Plaintext(PlaintextType::from(input.to_type()))).collect();

        // Compute the operation.
        let outputs = O::evaluate(&inputs.try_into().map_err(|_| anyhow!("Failed to prepare operands in evaluate"))?)?;
        // Compute the output type.
        let output_types = outputs
            .iter()
            .map(|output| RegisterType::Plaintext(PlaintextType::from(output.to_type())))
            .collect::<Vec<_>>();

        // Retrieve the expected output type.
        let expected_types = self.output_types(stack, &input_types)?;
        // Ensure there is the correct number of outputs.
        ensure!(
            expected_types.len() == NUM_DESTINATIONS,
            "Expected {} output type, found {}",
            NUM_DESTINATIONS,
            expected_types.len()
        );
        // Ensure the output types are correct.
        for (expected_type, output_type) in expected_types.iter().zip_eq(output_types.iter()) {
            ensure!(expected_type == output_type, "Expected output type {}, found {}", expected_type, output_type);
        }

        // Evaluate the operation and store the outputs.
        for (destination, output) in self.destinations.iter().zip_eq(outputs.into_iter()) {
            registers.store_literal(stack, destination, output)?;
        }
        Ok(())
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands", O::OPCODE, self.operands.len())
        }
        // Ensure the number of destinations is correct.
        if self.destinations.len() != NUM_DESTINATIONS {
            bail!(
                "Instruction '{}' expects {NUM_DESTINATIONS} destinations, found {} destinations",
                O::OPCODE,
                self.destinations.len()
            )
        }

        // Load the operands literals.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_literal_circuit(stack, operand)).try_collect()?;
        // Compute the operands register types.
        let input_types: Vec<_> =
            inputs.iter().map(|input| RegisterType::Plaintext(PlaintextType::from(input.to_type()))).collect();

        // Compute the operation.
        let outputs = O::execute(&inputs.try_into().map_err(|_| anyhow!("Failed to prepare operands in evaluate"))?)?;
        // Compute the output type.
        let output_types = outputs
            .iter()
            .map(|output| RegisterType::Plaintext(PlaintextType::from(output.to_type())))
            .collect::<Vec<_>>();

        // Retrieve the expected output type.
        let expected_types = self.output_types(stack, &input_types)?;
        // Ensure there are the correct number of outputs.
        ensure!(
            expected_types.len() == NUM_DESTINATIONS,
            "Expected {} output types, found {}",
            NUM_DESTINATIONS,
            expected_types.len()
        );
        // Ensure the output types are correct.
        for (expected_type, output_type) in expected_types.iter().zip_eq(output_types.iter()) {
            ensure!(expected_type == output_type, "Expected output type '{}', found {output_type}", expected_type);
        }

        // Evaluate the operation and store the output.
        for (destination, output) in self.destinations.iter().zip_eq(outputs.into_iter()) {
            registers.store_literal_circuit(stack, destination, output)?;
        }
        Ok(())
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, _stack: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} inputs, found {} inputs", O::OPCODE, input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands", O::OPCODE, self.operands.len())
        }

        // Convert all input types into `LiteralType`s. If any are not a `LiteralType`, return an error.
        let input_types = input_types
            .iter()
            .copied()
            .map(|input_type| match input_type {
                RegisterType::Plaintext(PlaintextType::Literal(literal_type)) => Ok(literal_type),
                RegisterType::Plaintext(PlaintextType::Struct(..)) => {
                    bail!("Expected literal type, found '{input_type}'")
                }
                RegisterType::Record(..) => bail!("Expected literal type, found '{input_type}'"),
                RegisterType::ExternalRecord(..) => bail!("Expected literal type, found '{input_type}'"),
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute the output type.
        let outputs =
            O::output_types(&input_types.try_into().map_err(|_| anyhow!("Failed to prepare operand types"))?)?;

        // Ensure the number of outputs is correct.
        if outputs.len() != NUM_DESTINATIONS {
            bail!("Instruction '{}' expects {NUM_DESTINATIONS} outputs, found {} outputs", O::OPCODE, outputs.len())
        }
        // Ensure the number of destinations is correct.
        if self.destinations.len() != NUM_DESTINATIONS {
            bail!(
                "Instruction '{}' expects {NUM_DESTINATIONS} destinations, found {} destinations",
                O::OPCODE,
                self.destinations.len()
            )
        }

        // Return the output types.
        Ok(outputs.into_iter().map(|output| RegisterType::Plaintext(PlaintextType::from(output))).collect())
    }
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> Parser for Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
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

        // Ensure the number of destination registers is within the bounds.
        if NUM_DESTINATIONS > N::MAX_OUTPUTS {
            N::halt(format!("The number of destination registers must be <= {}", N::MAX_OUTPUTS))
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

        // Initialize a vector to store the destination registers.
        let mut destinations = Vec::with_capacity(NUM_DESTINATIONS);
        // Initialize a tracker for the string.
        let mut string_tracker = string;
        // Parse the destination registers from the string.
        for _ in 0..NUM_DESTINATIONS {
            // Parse the destination register from the string.
            let (string, destination) = Register::parse(string_tracker)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Add the destination register to the vector.
            destinations.push(destination);
            // Update the string tracker.
            string_tracker = string;
        }

        Ok((string_tracker, Self { operands, destinations, _phantom: PhantomData }))
    }
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> FromStr for Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
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

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> Debug for Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
{
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> Display for Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
{
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            eprintln!("The number of operands must be <= {}", N::MAX_OPERANDS);
            return Err(fmt::Error);
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            eprintln!("The number of operands must be {}", NUM_OPERANDS);
            return Err(fmt::Error);
        }
        // Ensure the number of destination registers is within the bounds.
        if NUM_DESTINATIONS > N::MAX_OUTPUTS {
            eprintln!("The number of destination registers must be <= {}", N::MAX_OUTPUTS);
            return Err(fmt::Error);
        }
        // Ensure the number of destination registers is correct.
        if self.destinations.len() != NUM_DESTINATIONS {
            eprintln!("The number of destination registers must be {}", NUM_DESTINATIONS);
            return Err(fmt::Error);
        }

        // Print the operation.
        write!(f, "{} ", O::OPCODE)?;
        self.operands.iter().try_for_each(|operand| write!(f, "{} ", operand))?;
        write!(f, "into")?;
        self.destinations.iter().try_for_each(|destination| write!(f, " {}", destination))
    }
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> FromBytes for Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
{
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be <= {}", N::MAX_OPERANDS)));
        }
        // Ensure the number of outputs is within the bounds.
        if NUM_DESTINATIONS > N::MAX_OUTPUTS {
            return Err(error(format!("The number of outputs must be <= {}", N::MAX_OUTPUTS)));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(NUM_OPERANDS);
        // Read the operands.
        for _ in 0..NUM_OPERANDS {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Initialize the vector for the destination registers.
        let mut destinations = Vec::with_capacity(NUM_DESTINATIONS);
        // Read the destination registers.
        for _ in 0..NUM_DESTINATIONS {
            destinations.push(Register::read_le(&mut reader)?);
        }
        // Return the operation.
        Ok(Self { operands, destinations, _phantom: PhantomData })
    }
}

impl<
    N: Network,
    O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS, NUM_DESTINATIONS>,
    const NUM_OPERANDS: usize,
    const NUM_DESTINATIONS: usize,
> ToBytes for Literals<N, O, NUM_OPERANDS, NUM_DESTINATIONS>
{
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is within the bounds.
        if NUM_OPERANDS > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be <= {}", N::MAX_OPERANDS)));
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            return Err(error(format!("The number of operands must be {}", NUM_OPERANDS)));
        }
        // Ensure the number of destination registers is within the bounds.
        if NUM_DESTINATIONS > N::MAX_OUTPUTS {
            return Err(error(format!("The number of outputs must be <= {}", N::MAX_OUTPUTS)));
        }
        // Ensure the number of destination registers is correct.
        if self.destinations.len() != NUM_DESTINATIONS {
            return Err(error(format!("The number of outputs must be {}", NUM_DESTINATIONS)));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination registers.
        self.destinations.iter().try_for_each(|destination| destination.write_le(&mut writer))
    }
}
