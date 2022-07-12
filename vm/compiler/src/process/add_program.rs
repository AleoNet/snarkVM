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

use super::*;

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Adds a new program to the process.
    #[inline]
    pub fn add_program(&mut self, program: &Program<N>) -> Result<()> {
        // Retrieve the program ID.
        let program_id = program.id();

        // If the program already exists, ensure it is the same and return.
        if self.programs.contains_key(program_id) {
            // Retrieve the existing program.
            let existing_program = self.get_program(program_id)?;
            // Ensure the program is the same.
            match existing_program == program {
                true => return Ok(()),
                false => bail!("Program already exists but with different contents"),
            }
        }

        // Ensure the program is not already added.
        ensure!(!self.programs.contains_key(program_id), "Program '{program_id}' already exists");
        // Ensure the program imports all exist in the process already.
        for import in program.imports().keys() {
            ensure!(
                self.programs.contains_key(import),
                "Cannot add program '{program_id}' because its import '{import}' must be added first"
            );
        }

        // Construct the stack for the program.
        let mut stack = Stack::new(program.clone(), self.circuit_keys.clone())?;

        // Add all of the imports into the stack.
        for external_id in program.imports().keys() {
            // Retrieve the external stack for the import program ID.
            let external_stack = self.get_stack(external_id)?;
            // Add the external stack to the stack.
            stack.add_external_stack(external_stack)?;
        }
        // Add the program closures to the stack.
        for closure in program.closures().values() {
            // Compute the register types.
            let register_types = Self::process_closure(&stack, closure)?;
            // Add the register types to the stack.
            stack.add_closure_types(closure.name(), register_types)?;
        }
        // Add the program functions to the stack.
        for function in program.functions().values() {
            // Compute the register types.
            let register_types = Self::process_function(&stack, function)?;
            // Add the register types to the stack.
            stack.add_function_types(function.name(), register_types)?;
        }

        // Add the program to the process.
        self.programs.insert(*program_id, program.clone());
        // Add the stack to the process.
        self.stacks.insert(*program_id, stack);

        // Return success.
        Ok(())
    }
}

impl<N: Network, A: circuit::Aleo<Network = N, BaseField = N::Field>> Process<N, A> {
    /// Checks that the given closure is well-formed for the given program.
    fn process_closure(stack: &Stack<N, A>, closure: &Closure<N>) -> Result<RegisterTypes<N>> {
        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the inputs are well-formed.
        for input in closure.inputs() {
            // Check the input register type.
            Self::check_input(stack, &mut register_types, input.register(), input.register_type())?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in closure.instructions() {
            // Ensure the closure contains no call instructions.
            ensure!(instruction.opcode() != Opcode::Call, "A 'call' instruction is not allowed in closures");
            // Check the instruction opcode, operands, and destinations.
            Self::check_instruction(stack, &mut register_types, closure.name(), instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in closure.outputs() {
            // Check the output register type.
            Self::check_output(stack, &register_types, output.register(), output.register_type())?;
        }

        Ok(register_types)
    }

    /// Checks that the given function is well-formed for the given program.
    fn process_function(stack: &Stack<N, A>, function: &Function<N>) -> Result<RegisterTypes<N>> {
        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the inputs are well-formed.
        for input in function.inputs() {
            // Check the input register type.
            Self::check_input(stack, &mut register_types, input.register(), &RegisterType::from(*input.value_type()))?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in function.instructions() {
            // Check the instruction opcode, operands, and destinations.
            Self::check_instruction(stack, &mut register_types, function.name(), instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in function.outputs() {
            // Retrieve the register type and check the output register type.
            Self::check_output(stack, &register_types, output.register(), &RegisterType::from(*output.value_type()))?;
        }

        Ok(register_types)
    }

    /// Ensure the given input register is well-formed.
    fn check_input(
        stack: &Stack<N, A>,
        register_types: &mut RegisterTypes<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the interface is defined in the program.
                if !stack.program().contains_interface(interface_name) {
                    bail!("Interface '{interface_name}' in '{}' is not defined.", stack.program().id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !stack.program().contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", stack.program().id())
                }
            }
            RegisterType::ExternalRecord(locator) => {
                // Ensure the external record type is defined in the program.
                if !stack.contains_external_record(locator) {
                    bail!("External record '{locator}' in '{}' is not defined.", stack.program().id())
                }
            }
        };

        // Insert the input register.
        register_types.add_input(register.clone(), *register_type)?;

        // Ensure the register type and the input type match.
        if *register_type != register_types.get_type(stack, register)? {
            bail!("Input '{register}' does not match the expected input register type.")
        }
        Ok(())
    }

    /// Ensure the given output register is well-formed.
    fn check_output(
        stack: &Stack<N, A>,
        register_types: &RegisterTypes<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Inform the user the output register is an input register, to ensure this is intended behavior.
        if register_types.is_input(register) {
            eprintln!("Output {register} in '{}' is an input register, ensure this is intended", stack.program().id());
        }

        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the interface is defined in the program.
                if !stack.program().contains_interface(interface_name) {
                    bail!("Interface '{interface_name}' in '{}' is not defined.", stack.program().id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !stack.program().contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", stack.program().id())
                }
            }
            RegisterType::ExternalRecord(locator) => {
                // Ensure the external record type is defined in the program.
                if !stack.contains_external_record(locator) {
                    bail!("External record '{locator}' in '{}' is not defined.", stack.program().id())
                }
            }
        };

        // Ensure the register type and the output type match.
        if *register_type != register_types.get_type(stack, register)? {
            bail!(
                "Output '{register}' does not match the expected output register type: expected '{}', found '{}'",
                register_types.get_type(stack, register)?,
                register_type
            )
        }
        Ok(())
    }

    /// Ensures the given instruction is well-formed.
    fn check_instruction(
        stack: &Stack<N, A>,
        register_types: &mut RegisterTypes<N>,
        closure_or_function_name: &Identifier<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        // Ensure the opcode is well-formed.
        Self::check_instruction_opcode(stack, register_types, closure_or_function_name, instruction)?;

        // Initialize a vector to store the register types of the operands.
        let mut operand_types = Vec::with_capacity(instruction.operands().len());
        // Iterate over the operands, and retrieve the register type of each operand.
        for operand in instruction.operands() {
            // Retrieve and append the register type.
            operand_types.push(match operand {
                Operand::Literal(literal) => RegisterType::Plaintext(PlaintextType::from(literal.to_type())),
                Operand::Register(register) => register_types.get_type(stack, register)?,
            });
        }

        // Compute the destination register types.
        let destination_types = instruction.output_types(stack, &operand_types)?;

        // Insert the destination register.
        for (destination, destination_type) in
            instruction.destinations().into_iter().zip_eq(destination_types.into_iter())
        {
            // Ensure the destination register is a locator (and does not reference a member).
            ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
            // Insert the destination register.
            register_types.add_destination(destination, destination_type)?;
        }
        Ok(())
    }

    /// Ensures the opcode is a valid opcode and corresponds to the correct instruction.
    /// This method is called when adding a new closure or function to the program.
    fn check_instruction_opcode(
        stack: &Stack<N, A>,
        register_types: &RegisterTypes<N>,
        closure_or_function_name: &Identifier<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        match instruction.opcode() {
            Opcode::Literal(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Self::is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                // Ensure the instruction is not the cast operation.
                ensure!(!matches!(instruction, Instruction::Cast(..)), "Instruction '{instruction}' is a 'cast'.");
                // Ensure the instruction has one destination register.
                ensure!(
                    instruction.destinations().len() == 1,
                    "Instruction '{instruction}' has multiple destinations."
                );
            }
            Opcode::Call => {
                // Retrieve the call operation.
                let call = match instruction {
                    Instruction::Call(call) => call,
                    _ => bail!("Instruction '{instruction}' is not a call operation."),
                };

                // Retrieve the operator.
                match call.operator() {
                    CallOperator::Locator(locator) => {
                        // Retrieve the program ID.
                        let program_id = locator.program_id();
                        // Retrieve the resource from the locator.
                        let resource = locator.resource();

                        // Ensure the locator does not reference the current program.
                        if stack.program().id() == program_id {
                            bail!("Locator '{locator}' does not reference an external program.");
                        }
                        // Ensure the current program contains an import for this external program.
                        if !stack.program().imports().keys().contains(program_id) {
                            bail!("External program '{}' is not imported by '{program_id}'.", locator.program_id());
                        }

                        // Retrieve the program.
                        let external = stack.get_external_program(program_id)?;
                        // Ensure the function or closure exists in the program.
                        if !external.contains_function(resource) && !external.contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", external.id())
                        }
                    }
                    CallOperator::Resource(resource) => {
                        // Ensure the resource does not reference this closure or function.
                        if resource == closure_or_function_name {
                            bail!("Cannot invoke 'call' to self (in '{resource}'): self-recursive call.");
                        }
                        // Ensure the function or closure exists in the program.
                        if !stack.program().contains_function(resource) && !stack.program().contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", stack.program().id())
                        }
                    }
                }
            }
            Opcode::Cast => {
                // Retrieve the cast operation.
                let operation = match instruction {
                    Instruction::Cast(operation) => operation,
                    _ => bail!("Instruction '{instruction}' is not a cast operation."),
                };

                // Ensure the instruction has one destination register.
                ensure!(
                    instruction.destinations().len() == 1,
                    "Instruction '{instruction}' has multiple destinations."
                );

                // Ensure the casted register type is defined.
                match operation.register_type() {
                    RegisterType::Plaintext(PlaintextType::Literal(..)) => {
                        bail!("Casting to literal is currently unsupported")
                    }
                    RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                        // Ensure the interface name exists in the program.
                        if !stack.program().contains_interface(interface_name) {
                            bail!("Interface '{interface_name}' is not defined.")
                        }
                        // Retrieve the interface.
                        let interface = stack.program().get_interface(interface_name)?;
                        // Ensure the operand types match the interface.
                        register_types.matches_interface(stack, instruction.operands(), &interface)?;
                    }
                    RegisterType::Record(record_name) => {
                        // Ensure the record type is defined in the program.
                        if !stack.program().contains_record(record_name) {
                            bail!("Record '{record_name}' is not defined.")
                        }
                        // Retrieve the record type.
                        let record_type = stack.program().get_record(record_name)?;
                        // Ensure the operand types match the record type.
                        register_types.matches_record(stack, instruction.operands(), &record_type)?;
                    }
                    RegisterType::ExternalRecord(_locator) => {
                        bail!("Illegal operation: Cannot cast to an external record.")
                    }
                }
            }
            Opcode::Commit(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Self::is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                // Ensure the instruction belongs to the defined set.
                if ![
                    "commit.bhp256",
                    "commit.bhp512",
                    "commit.bhp768",
                    "commit.bhp1024",
                    "commit.ped64",
                    "commit.ped128",
                ]
                .contains(&opcode)
                {
                    bail!("Instruction '{instruction}' is not the opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                // match opcode {
                //     "commit.bhp256" => ensure!(
                //         matches!(instruction, Instruction::CommitBHP256(..)),
                //         "Instruction '{instruction}' is not the opcode '{opcode}'."
                //     ),
                // }
            }
            Opcode::Hash(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Self::is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                // Ensure the instruction belongs to the defined set.
                if ![
                    "hash.bhp256",
                    "hash.bhp512",
                    "hash.bhp768",
                    "hash.bhp1024",
                    "hash.ped64",
                    "hash.ped128",
                    "hash.psd2",
                    "hash.psd4",
                    "hash.psd8",
                ]
                .contains(&opcode)
                {
                    bail!("Instruction '{instruction}' is not the opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                // match opcode {
                //     "hash.bhp256" => ensure!(
                //         matches!(instruction, Instruction::HashBHP256(..)),
                //         "Instruction '{instruction}' is not the opcode '{opcode}'."
                //     ),
                // }
            }
        }
        Ok(())
    }

    /// Returns `true` if the given name is a reserved opcode.
    fn is_reserved_opcode(name: &Identifier<N>) -> bool {
        // Convert the given name to a string.
        let name = name.to_string();
        // Check if the given name matches the root of any opcode (the first part, up to the first '.').
        Instruction::<N>::OPCODES.iter().any(|opcode| (**opcode).split('.').next() == Some(&name))
    }
}
