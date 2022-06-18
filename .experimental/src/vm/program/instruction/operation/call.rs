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

use crate::vm::{Opcode, Operand, Program, Stack};
use console::{
    network::prelude::*,
    program::{Identifier, Register, RegisterType},
};

/// Calls the operands into the declared type.
/// i.e. `call transfer r0.owner 0u64 r1.amount into r1 r2;`
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Call<N: Network> {
    /// The name of the closure.
    name: Identifier<N>,
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination registers.
    destinations: Vec<Register<N>>,
}

impl<N: Network> Call<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Call
    }

    /// Return the name of the closure.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        &self.operands
    }

    /// Returns the destination registers.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        self.destinations.clone()
    }
}

impl<N: Network> Call<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(&self, stack: &mut Stack<N>) -> Result<()> {
        // Initialize a vector to store the operand values.
        let mut inputs = Vec::with_capacity(self.operands.len());
        // Load the operands values.
        self.operands.iter().try_for_each(|operand| {
            // Load and append the value.
            inputs.push(stack.load(operand)?);
            // Move to the next iteration.
            Ok::<_, Error>(())
        })?;

        // Retrieve the closure from the program.
        let closure = stack.program().get_closure(&self.name)?;
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }
        // Ensure there are input statements in the closure.
        ensure!(!closure.inputs().is_empty(), "Cannot evaluate a closure without input statements");
        // Ensure there are instructions in the closure.
        ensure!(!closure.instructions().is_empty(), "Cannot evaluate a closure without instructions");

        // Retrieve the register types.
        let register_types = stack.program().get_closure_registers(&self.name)?;

        // Initialize the stack.
        let mut closure_stack = Stack::new(stack.program().clone(), register_types.clone())?;

        // Ensure the inputs match the expected closure inputs.
        for (input, (register, register_type)) in inputs.iter().zip_eq(register_types.to_input_types()) {
            // Ensure the input matches the declared type in the register.
            closure_stack.program().matches_register(input, &register_type)?;
            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
            // TODO (howardwu): OR if input is a record, forbid and error.
            // Assign the input value to the register.
            closure_stack.input_registers().insert(register.locator(), input.clone());
        }

        // Evaluate the instructions.
        closure.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut closure_stack))?;

        // Initialize a vector to store the outputs.
        let mut outputs = Vec::with_capacity(closure.outputs().len());
        // Load the outputs.
        for (register, register_type) in closure_stack.to_output_types() {
            // Retrieve the output from the register.
            let output = closure_stack.load(&Operand::Register(register.clone()))?;
            // Ensure the output matches the declared type in the register.
            closure_stack.program().matches_register(&output, &register_type)?;
            // Insert the output into the outputs.
            outputs.push(output);
        }

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.iter().zip_eq(self.destinations.iter()) {
            // Assign the output to the register.
            stack.store(register, output.clone())?;
        }

        Ok(())
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, program: &Program<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Retrieve the closure.
        let closure = program.get_closure(&self.name)?;
        // Ensure there are input statements in the closure.
        ensure!(!closure.inputs().is_empty(), "Cannot evaluate a closure without input statements");
        // Ensure there are instructions in the closure.
        ensure!(!closure.instructions().is_empty(), "Cannot evaluate a closure without instructions");

        // Ensure the number of operands matches the number of input statements.
        if closure.inputs().len() != self.operands.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), self.operands.len())
        }
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != input_types.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), input_types.len())
        }
        // Ensure the number of destinations matches the number of output statements.
        if closure.outputs().len() != self.destinations.len() {
            bail!("Expected {} outputs, found {}", closure.outputs().len(), self.destinations.len())
        }

        // Return the output register types.
        Ok(closure.outputs().iter().map(|output| *output.register_type()).collect())
    }
}

impl<N: Network> Parser for Call<N> {
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

        /// Parses a destination register from the string.
        fn parse_destination<N: Network>(string: &str) -> ParserResult<Register<N>> {
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the destination from the string.
            Register::parse(string)
        }

        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the name of the call from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the operands from the string.
        let (string, operands) = map_res(many1(parse_operand), |operands: Vec<Operand<N>>| {
            // Ensure the number of operands is within the bounds.
            match operands.len() <= N::MAX_OPERANDS {
                true => Ok(operands),
                false => Err(error("Failed to parse 'call' opcode: too many operands")),
            }
        })(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destinations) = map_res(many1(parse_destination), |destinations: Vec<Register<N>>| {
            // Ensure the number of destination registers is within the bounds.
            match destinations.len() <= N::MAX_OPERANDS {
                true => Ok(destinations),
                false => Err(error("Failed to parse 'call' opcode: too many destination registers")),
            }
        })(string)?;

        Ok((string, Self { name, operands, destinations }))
    }
}

impl<N: Network> FromStr for Call<N> {
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

impl<N: Network> Debug for Call<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Call<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is within the bounds.
        if self.operands.len().is_zero() || self.operands.len() > N::MAX_OPERANDS {
            eprintln!("The number of operands must be nonzero and <= {}", N::MAX_OPERANDS);
            return Err(fmt::Error);
        }
        // Ensure the number of destinations is within the bounds.
        if self.destinations.len().is_zero() || self.destinations.len() > N::MAX_OPERANDS {
            eprintln!("The number of destinations must be nonzero and <= {}", N::MAX_OPERANDS);
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} {}", Self::opcode(), self.name)?;
        self.operands.iter().try_for_each(|operand| write!(f, " {operand}"))?;
        write!(f, " into")?;
        self.destinations.iter().try_for_each(|destination| write!(f, " {destination}"))
    }
}

impl<N: Network> FromBytes for Call<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the name of the call.
        let name = Identifier::read_le(&mut reader)?;

        // Read the number of operands.
        let num_operands = u8::read_le(&mut reader)? as usize;
        // Ensure the number of operands is within the bounds.
        if num_operands.is_zero() || num_operands > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be nonzero and <= {}", N::MAX_OPERANDS)));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(num_operands);
        // Read the operands.
        for _ in 0..num_operands {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Read the number of destination registers.
        let num_destinations = u8::read_le(&mut reader)? as usize;
        // Ensure the number of destinations is within the bounds.
        if num_destinations.is_zero() || num_destinations > N::MAX_OPERANDS {
            return Err(error(format!("The number of destinations must be nonzero and <= {}", N::MAX_OPERANDS)));
        }

        // Initialize the vector for the destinations.
        let mut destinations = Vec::with_capacity(num_destinations);
        // Read the destination registers.
        for _ in 0..num_destinations {
            destinations.push(Register::read_le(&mut reader)?);
        }

        // Return the operation.
        Ok(Self { name, operands, destinations })
    }
}

impl<N: Network> ToBytes for Call<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is within the bounds.
        if self.operands.len().is_zero() || self.operands.len() > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be nonzero and <= {}", N::MAX_OPERANDS)));
        }
        // Ensure the number of destinations is within the bounds.
        if self.destinations.len().is_zero() || self.destinations.len() > N::MAX_OPERANDS {
            return Err(error(format!("The number of destinations must be nonzero and <= {}", N::MAX_OPERANDS)));
        }

        // Write the name of the call.
        self.name.write_le(&mut writer)?;
        // Write the number of operands.
        (self.operands.len() as u8).write_le(&mut writer)?;
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the number of destination register.
        (self.destinations.len() as u8).write_le(&mut writer)?;
        // Write the destination registers.
        self.destinations.iter().try_for_each(|destination| destination.write_le(&mut writer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{network::Testnet3, program::Identifier};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, call) =
            Call::<CurrentNetwork>::parse("call transfer r0.owner r0.balance r0.token_amount into r1 r2 r3").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(call.name, Identifier::from_str("transfer").unwrap(), "The name of the call is incorrect");
        assert_eq!(call.operands.len(), 3, "The number of operands is incorrect");
        assert_eq!(
            call.operands[0],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("owner").unwrap()])),
            "The first operand is incorrect"
        );
        assert_eq!(
            call.operands[1],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("balance").unwrap()])),
            "The second operand is incorrect"
        );
        assert_eq!(
            call.operands[2],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("token_amount").unwrap()])),
            "The third operand is incorrect"
        );
        assert_eq!(call.destinations.len(), 3, "The number of destinations is incorrect");
        assert_eq!(call.destinations[0], Register::Locator(1), "The first destination register is incorrect");
        assert_eq!(call.destinations[1], Register::Locator(2), "The second destination register is incorrect");
        assert_eq!(call.destinations[2], Register::Locator(3), "The third destination register is incorrect");
    }
}
