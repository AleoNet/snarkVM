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

use crate::{CallStack, Opcode, Operand, Stack};
use console::{
    network::prelude::*,
    program::{Identifier, Locator, Register, RegisterType, Request, ValueType},
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
        alt((map(Locator::parse, CallOperator::Locator), map(Identifier::parse, CallOperator::Resource)))(string)
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
    pub fn execute<A: circuit::Aleo<Network = N, BaseField = N::Field>>(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| stack.load_circuit(operand)).try_collect()?;

        // Retrieve the substack and resource.
        let (mut substack, resource) = match &self.operator {
            // Retrieve the call stack and resource from the locator.
            CallOperator::Locator(locator) => {
                (stack.get_external_stack(locator.program_id())?.clone(), locator.resource())
            }
            CallOperator::Resource(resource) => (stack.clone(), resource),
        };

        // If the operator is a closure, retrieve the closure and compute the output.
        let outputs = if let Ok(closure) = substack.program().get_closure(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
            }
            // Execute the closure, and load the outputs.
            substack.execute_closure(&closure, &inputs, stack.call_stack())?
        }
        // If the operator is a function, retrieve the function and compute the output.
        else if let Ok(function) = substack.program().get_function(resource) {
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != inputs.len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
            }

            // Retrieve the number of public variables in the circuit.
            let num_public = A::num_public();

            // Initialize an RNG.
            let rng = &mut rand::thread_rng();

            use circuit::Eject;
            // Eject the existing circuit.
            let r1cs = A::eject_r1cs_and_reset();
            let (request, response) = match stack.call_stack() {
                // If the circuit is in authorize mode, then add any external calls to the stack.
                CallStack::Authorize(_, private_key, authorization) => {
                    // Eject the circuit inputs.
                    let inputs = inputs.eject_value();
                    // Retrieve the input types.
                    let input_types = function.input_types();
                    // Ensure the inputs match their expected types.
                    inputs
                        .iter()
                        .zip_eq(&input_types)
                        .try_for_each(|(input, input_type)| substack.matches_value_type(input, input_type))?;

                    // Compute the request.
                    let request = Request::sign(
                        &private_key,
                        *substack.program_id(),
                        *function.name(),
                        &inputs,
                        &input_types,
                        rng,
                    )?;

                    // Retrieve the call stack.
                    let mut call_stack = stack.call_stack();
                    // Push the request onto the call stack.
                    call_stack.push(request.clone())?;

                    // Add the request to the authorization.
                    authorization.push(request.clone());

                    // Execute the request.
                    let response = substack.execute(call_stack, rng)?;

                    // Return the request and response.
                    (request, response)
                }
                // If the circuit is in execute mode, then evaluate and execute the instructions.
                CallStack::Execute(authorization, ..) => {
                    // Eject the circuit inputs.
                    let inputs = inputs.eject_value();
                    // Retrieve the input types.
                    let input_types = function.input_types();
                    // Ensure the inputs match their expected types.
                    inputs
                        .iter()
                        .zip_eq(&input_types)
                        .try_for_each(|(input, input_type)| substack.matches_value_type(input, input_type))?;

                    // Retrieve the next request (without popping it).
                    let request = authorization.peek_next()?;
                    // Ensure the inputs match the original inputs.
                    request.inputs().iter().zip_eq(&inputs).try_for_each(|(request_input, input)| {
                        ensure!(request_input == input, "Inputs do not match in a 'call' instruction.");
                        Ok(())
                    })?;

                    // Evaluate the function, and load the outputs.
                    let console_outputs = substack.evaluate_function(&function, &inputs)?;
                    // Execute the request.
                    let response = substack.execute(stack.call_stack(), rng)?;
                    // Ensure the values are equal.
                    if console_outputs != response.outputs() {
                        #[cfg(debug_assertions)]
                        eprintln!("\n{:#?} != {:#?}\n", console_outputs, response.outputs());
                        bail!("Function '{}' outputs do not match in a 'call' instruction.", function.name())
                    }
                    // Return the request and response.
                    (request, response)
                }
            };
            // Inject the existing circuit.
            A::inject_r1cs(r1cs);

            // Ensure the inputs matches the expected value types.
            request.inputs().iter().zip_eq(&function.input_types()).try_for_each(|(input, input_type)| {
                // Ensure the input matches its expected type.
                substack.matches_value_type(input, input_type)
            })?;

            // Ensure the outputs matches the expected value types.
            response.outputs().iter().zip_eq(&function.output_types()).try_for_each(|(output, output_type)| {
                // Ensure the output matches its expected type.
                substack.matches_value_type(output, output_type)
            })?;

            use circuit::Inject;

            // Retrieve the number of inputs.
            let num_inputs = function.inputs().len();
            // Inject the program ID as `Mode::Constant`.
            let program_id = circuit::ProgramID::constant(*substack.program_id());
            // Retrieve the circuit caller from the stack.
            let caller = stack.circuit_caller()?;

            // Ensure the number of public variables remains the same.
            ensure!(A::num_public() == num_public, "Forbidden: 'call' injected excess public variables");

            // Inject the `tvk` (from the request) as `Mode::Private`.
            let tvk = circuit::Field::new(circuit::Mode::Private, *request.tvk());
            // Inject the input IDs (from the request) as `Mode::Public`.
            let input_ids = request
                .input_ids()
                .iter()
                .map(|input_id| circuit::InputID::new(circuit::Mode::Public, *input_id))
                .collect::<Vec<_>>();
            // Ensure the candidate input IDs match their computed inputs.
            A::assert(circuit::Request::check_input_ids(&input_ids, &inputs, caller, &program_id, &tvk));

            // Inject the response as `Mode::Private` (with the IDs as `Mode::Public`).
            let response = circuit::Response::new(circuit::Mode::Private, response);
            // Ensure the response matches its declared IDs.
            A::assert(response.verify(&program_id, num_inputs, &tvk));

            // Return the circuit outputs.
            response.outputs().to_vec()
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
        let (is_external, program, resource) = match &self.operator {
            // Retrieve the program and resource from the locator.
            CallOperator::Locator(locator) => {
                (true, stack.get_external_program(locator.program_id())?, locator.resource())
            }
            CallOperator::Resource(resource) => (false, stack.program(), resource),
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
            function
                .output_types()
                .into_iter()
                .map(|output_type| match (is_external, output_type) {
                    // If the output is a record and the function is external, return the external record type.
                    (true, ValueType::Record(record_name)) => Ok(RegisterType::ExternalRecord(Locator::from_str(
                        &format!("{}/{}", program.id(), record_name),
                    )?)),
                    // Else, return the register type.
                    (_, _) => Ok(RegisterType::from(output_type)),
                })
                .collect::<Result<Vec<_>>>()
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
    use console::{network::Testnet3, program::Identifier};

    type CurrentNetwork = Testnet3;

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
