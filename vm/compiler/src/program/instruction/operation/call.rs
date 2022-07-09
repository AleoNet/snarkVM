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

use crate::{Opcode, Operand, Stack, StackCall, StackMode};
use console::{
    network::prelude::*,
    program::{Identifier, Locator, Register, RegisterType, ValueType},
};

/// The operator references a function name or closure name.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum CallOperator<N: Network> {
    /// The reference to a non-local function or closure.
    Locator(Locator<N>),
    /// The reference to a local function or closure.
    Resource(Identifier<N>),
}

impl<N: Network> Parser for CallOperator<N> {
    /// Parses a string into an operator.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((map(Identifier::parse, CallOperator::Resource), map(Locator::parse, CallOperator::Locator)))(string)
    }
}

impl<N: Network> FromStr for CallOperator<N> {
    type Err = Error;

    /// Parses a string into an operator.
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

impl<N: Network> Debug for CallOperator<N> {
    /// Prints the operator as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for CallOperator<N> {
    /// Prints the operator to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CallOperator::Locator(locator) => Display::fmt(locator, f),
            CallOperator::Resource(resource) => Display::fmt(resource, f),
        }
    }
}

impl<N: Network> FromBytes for CallOperator<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Match the variant.
        match variant {
            0 => Ok(CallOperator::Locator(Locator::read_le(&mut reader)?)),
            1 => Ok(CallOperator::Resource(Identifier::read_le(&mut reader)?)),
            _ => Err(error("Failed to read CallOperator. Invalid variant.")),
        }
    }
}

impl<N: Network> ToBytes for CallOperator<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            CallOperator::Locator(locator) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the locator.
                locator.write_le(&mut writer)
            }
            CallOperator::Resource(resource) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the resource.
                resource.write_le(&mut writer)
            }
        }
    }
}

/// Calls the operands into the declared type.
/// i.e. `call transfer r0.owner 0u64 r1.amount into r1 r2;`
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Call<N: Network> {
    /// The reference.
    operator: CallOperator<N>,
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

    /// Return the operator.
    #[inline]
    pub const fn operator(&self) -> &CallOperator<N> {
        &self.operator
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
    pub fn evaluate<A: circuit::Aleo<Network = N>>(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| stack.load(operand)).try_collect()?;

        // Retrieve the call stack and resource.
        let (mut call_stack, resource) = match &self.operator {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                (stack.get_external_stack(locator.program_id())?.clone(), locator.resource())
            }
            CallOperator::Resource(resource) => (stack.clone(), resource),
        };

        // If the operator is a closure, retrieve the closure and compute the output.
        let outputs = if let Ok(closure) = call_stack.program().get_closure(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
            }
            // Evaluate the closure, and load the outputs.
            call_stack.evaluate_closure(&closure, &inputs)?
        }
        // If the operator is a function, retrieve the function and compute the output.
        else if let Ok(function) = call_stack.program().get_function(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
            }
            // Evaluate the function, and load the outputs.
            call_stack.evaluate_function(&function, &inputs)?
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", self.operator)
        };

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.into_iter().zip_eq(&self.destinations) {
            // Assign the output to the register.
            stack.store(register, output)?;
        }

        Ok(())
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| stack.load_circuit(operand)).try_collect()?;

        // Retrieve the call stack and resource.
        let (mut call_stack, resource) = match &self.operator {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                (stack.get_external_stack(locator.program_id())?.clone(), locator.resource())
            }
            CallOperator::Resource(resource) => (stack.clone(), resource),
        };

        // If the operator is a closure, retrieve the closure and compute the output.
        let outputs = if let Ok(closure) = call_stack.program().get_closure(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
            }
            // Execute the closure, and load the outputs.
            call_stack.execute_closure(&closure, &inputs, stack.stack_mode())?
        }
        // If the operator is a function, retrieve the function and compute the output.
        else if let Ok(function) = call_stack.program().get_function(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
            }

            // Retrieve the number of public variables in the circuit.
            let num_public = A::num_public();

            // Eject the existing circuit.
            let r1cs = A::eject_r1cs_and_reset();
            let console_outputs = {
                use circuit::Eject;

                // Execute the function, and load the outputs.
                let circuit_outputs = call_stack.execute_function(&function, &inputs, stack.stack_mode())?;

                // If the circuit is in authorize mode, then add any external calls to the stack.
                if stack.stack_mode() == StackMode::Authorize {
                    // Add the external call to the stack, including external calls from the `call_stack` as subcalls.
                    stack.add_external_call(StackCall::new(
                        call_stack.external_calls(),
                        call_stack.program_id(),
                        function.name(),
                        inputs.eject_value(),
                        function.input_types(),
                    ));
                }

                // If the circuit is in execute mode, then evaluate the instructions.
                if stack.stack_mode() == StackMode::Execute {
                    // Evaluate the function, and load the outputs.
                    let console_outputs = call_stack.evaluate_function(&function, &inputs.eject_value())?;
                    // Ensure the values are equal.
                    if console_outputs == circuit_outputs.eject_value() {
                        bail!("Function '{}' outputs do not match in a 'call' instruction.", function.name())
                    }
                }

                // Return the console outputs.
                circuit_outputs.eject_value()
            };
            // Inject the existing circuit.
            A::inject_r1cs(r1cs);

            // Inject the circuit outputs.
            let outputs = console_outputs
                .into_iter()
                .zip_eq(&function.output_types())
                .map(|(output, output_type)| {
                    use circuit::Inject;

                    match output_type {
                        ValueType::Constant(plaintext) => {
                            // Ensure the output matches its expected type.
                            call_stack
                                .program()
                                .matches_register_type(&output, &RegisterType::Plaintext(*plaintext))?;
                            // Inject the constant output as `Mode::Constant`.
                            Ok(circuit::Value::new(circuit::Mode::Constant, output))
                        }
                        ValueType::Public(plaintext) => {
                            // Ensure the output matches its expected type.
                            call_stack
                                .program()
                                .matches_register_type(&output, &RegisterType::Plaintext(*plaintext))?;
                            // Inject the public output as `Mode::Private`.
                            Ok(circuit::Value::new(circuit::Mode::Private, output))
                        }
                        ValueType::Private(plaintext) => {
                            // Ensure the output matches its expected type.
                            call_stack
                                .program()
                                .matches_register_type(&output, &RegisterType::Plaintext(*plaintext))?;
                            // Inject the private output as `Mode::Private`.
                            Ok(circuit::Value::new(circuit::Mode::Private, output))
                        }
                        ValueType::Record(record) => {
                            // Ensure the output matches its expected type.
                            call_stack.program().matches_register_type(&output, &RegisterType::Record(*record))?;
                            // Inject the record output as `Mode::Private`.
                            Ok(circuit::Value::new(circuit::Mode::Private, output))
                        }
                        ValueType::ExternalRecord(locator) => {
                            // Retrieve the external program.
                            let external_program = call_stack.get_external_program(locator.program_id())?;
                            // Ensure the output matches its expected type from the external program.
                            external_program
                                .matches_register_type(&output, &RegisterType::Record(*locator.resource()))?;
                            // Inject the external record output as `Mode::Private`.
                            Ok(circuit::Value::new(circuit::Mode::Private, output))
                        }
                    }
                })
                .collect::<Result<Vec<_>>>()?;

            // Ensure the number of public variables remains the same.
            ensure!(A::num_public() == num_public, "Forbidden: 'call' injected excess public variables");

            // Return the circuit outputs.
            outputs
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", self.operator)
        };

        // Assign the outputs to the destination registers.
        for (output, register) in outputs.into_iter().zip_eq(&self.destinations) {
            // Assign the output to the register.
            stack.store_circuit(register, output)?;
        }

        Ok(())
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N, A>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Retrieve the program and resource.
        let (program, resource) = match &self.operator {
            // Retrieve the program and resource from the locator.
            CallOperator::Locator(locator) => (stack.get_external_program(locator.program_id())?, locator.resource()),
            CallOperator::Resource(resource) => (stack.program(), resource),
        };

        // If the operator is a closure, retrieve the closure and compute the output types.
        if let Ok(closure) = program.get_closure(resource) {
            // Ensure the number of operands matches the number of input statements.
            if closure.inputs().len() != self.operands.len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), self.operands.len())
            }
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != input_types.len() {
                bail!("Expected {} input types, found {}", closure.inputs().len(), input_types.len())
            }
            // Ensure the number of destinations matches the number of output statements.
            if closure.outputs().len() != self.destinations.len() {
                bail!("Expected {} outputs, found {}", closure.outputs().len(), self.destinations.len())
            }
            // Return the output register types.
            Ok(closure.outputs().iter().map(|output| *output.register_type()).collect())
        }
        // If the operator is a function, retrieve the function and compute the output types.
        else if let Ok(function) = program.get_function(resource) {
            // Ensure the number of operands matches the number of input statements.
            if function.inputs().len() != self.operands.len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), self.operands.len())
            }
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != input_types.len() {
                bail!("Expected {} input types, found {}", function.inputs().len(), input_types.len())
            }
            // Ensure the number of destinations matches the number of output statements.
            if function.outputs().len() != self.destinations.len() {
                bail!("Expected {} outputs, found {}", function.outputs().len(), self.destinations.len())
            }
            // Return the output register types.
            Ok(function.outputs().iter().map(|output| RegisterType::from(*output.value_type())).collect())
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", self.operator)
        }
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
        let (string, operator) = CallOperator::parse(string)?;
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

        Ok((string, Self { operator, operands, destinations }))
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
        write!(f, "{} {}", Self::opcode(), self.operator)?;
        self.operands.iter().try_for_each(|operand| write!(f, " {operand}"))?;
        write!(f, " into")?;
        self.destinations.iter().try_for_each(|destination| write!(f, " {destination}"))
    }
}

impl<N: Network> FromBytes for Call<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the operator of the call.
        let operator = CallOperator::read_le(&mut reader)?;

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
        Ok(Self { operator, operands, destinations })
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
        self.operator.write_le(&mut writer)?;
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
    use circuit::network::AleoV0;
    use console::{network::Testnet3, program::Identifier};

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_parse() {
        let (string, call) =
            Call::<CurrentNetwork>::parse("call transfer r0.owner r0.balance r0.token_amount into r1 r2 r3").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(call.operator, CallOperator::from_str("transfer").unwrap(), "The call operator is incorrect");
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
