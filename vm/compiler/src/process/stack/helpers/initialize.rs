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

impl<N: Network> Stack<N> {
    /// Initializes a new stack, given the process and program.
    #[inline]
    pub(crate) fn initialize(process: &Process<N>, program: &Program<N>) -> Result<Self> {
        // Construct the stack for the program.
        let mut stack = Self {
            program: program.clone(),
            external_stacks: Default::default(),
            program_types: Default::default(),
            universal_srs: process.universal_srs().clone(),
            proving_keys: Default::default(),
            verifying_keys: Default::default(),
        };

        // Add all of the imports into the stack.
        for import in program.imports().keys() {
            // Ensure the program imports all exist in the process already.
            if !process.contains_program(import) {
                bail!("Cannot add program '{}' because its import '{import}' must be added first", program.id())
            }
            // Retrieve the external stack for the import program ID.
            let external_stack = process.get_stack(import)?;
            // Add the external stack to the stack.
            stack.insert_external_stack(external_stack.clone())?;
        }
        // Add the program closures to the stack.
        for closure in program.closures().values() {
            // Add the closure to the stack.
            stack.insert_closure(closure)?;
        }
        // Add the program functions to the stack.
        for function in program.functions().values() {
            // Add the function to the stack.
            stack.insert_function(function)?;
        }
        // Return the stack.
        Ok(stack)
    }
}

impl<N: Network> Stack<N> {
    /// Inserts the given external stack to the stack.
    #[inline]
    fn insert_external_stack(&mut self, external_stack: Stack<N>) -> Result<()> {
        // Retrieve the program ID.
        let program_id = *external_stack.program_id();
        // Ensure the external stack is not already added.
        ensure!(!self.external_stacks.contains_key(&program_id), "Program '{program_id}' already exists");
        // Ensure the program exists in the main program imports.
        ensure!(self.program.contains_import(&program_id), "'{program_id}' does not exist in the main program imports");
        // Ensure the external stack is not for the main program.
        ensure!(self.program.id() != external_stack.program_id(), "External stack program cannot be the main program");
        // Add the external stack to the stack.
        self.external_stacks.insert(program_id, external_stack);
        // Return success.
        Ok(())
    }

    /// Inserts the given closure to the stack.
    #[inline]
    fn insert_closure(&mut self, closure: &Closure<N>) -> Result<()> {
        // Retrieve the closure name.
        let name = closure.name();
        // Ensure the closure name is not already added.
        ensure!(!self.program_types.contains_key(name), "Closure '{name}' already exists");

        // Compute the register types.
        let register_types = self.compute_closure_types(closure)?;
        // Add the closure name and register types to the stack.
        self.program_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }

    /// Adds the given function name and register types to the stack.
    #[inline]
    fn insert_function(&mut self, function: &Function<N>) -> Result<()> {
        // Retrieve the function name.
        let name = function.name();
        // Ensure the function name is not already added.
        ensure!(!self.program_types.contains_key(name), "Function '{name}' already exists");

        // Compute the register types.
        let register_types = self.compute_function_types(function)?;
        // Add the function name and register types to the stack.
        self.program_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }
}

impl<N: Network> Stack<N> {
    /// Checks that the given closure is well-formed for the given program.
    #[inline]
    fn compute_closure_types(&self, closure: &Closure<N>) -> Result<RegisterTypes<N>> {
        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the inputs are well-formed.
        for input in closure.inputs() {
            // Check the input register type.
            self.check_input(&mut register_types, input.register(), input.register_type())?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in closure.instructions() {
            // Ensure the closure contains no call instructions.
            ensure!(instruction.opcode() != Opcode::Call, "A 'call' instruction is not allowed in closures");
            // Check the instruction opcode, operands, and destinations.
            self.check_instruction(&mut register_types, closure.name(), instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in closure.outputs() {
            // Check the output register type.
            self.check_output(&register_types, output.register(), output.register_type())?;
        }

        Ok(register_types)
    }

    /// Checks that the given function is well-formed for the given program.
    #[inline]
    fn compute_function_types(&self, function: &Function<N>) -> Result<RegisterTypes<N>> {
        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the inputs are well-formed.
        for input in function.inputs() {
            // TODO (howardwu): In order to support constant inputs, update `Self::deploy()` to allow
            //  the caller to provide optional constant inputs (instead of sampling random constants).
            //  Then, this check can be removed to enable support for constant inputs in functions.
            ensure!(!matches!(input.value_type(), ValueType::Constant(..)), "Constant inputs are not supported (yet)");

            // Check the input register type.
            self.check_input(&mut register_types, input.register(), &RegisterType::from(*input.value_type()))?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in function.instructions() {
            // Check the instruction opcode, operands, and destinations.
            self.check_instruction(&mut register_types, function.name(), instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in function.outputs() {
            // Retrieve the register type and check the output register type.
            self.check_output(&register_types, output.register(), &RegisterType::from(*output.value_type()))?;
        }

        Ok(register_types)
    }
}

impl<N: Network> Stack<N> {
    /// Ensure the given input register is well-formed.
    #[inline]
    fn check_input(
        &self,
        register_types: &mut RegisterTypes<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the interface is defined in the program.
                if !self.program.contains_interface(interface_name) {
                    bail!("Interface '{interface_name}' in '{}' is not defined.", self.program.id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !self.program.contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", self.program.id())
                }
            }
            RegisterType::ExternalRecord(locator) => {
                // Ensure the external record type is defined in the program.
                if !self.contains_external_record(locator) {
                    bail!("External record '{locator}' in '{}' is not defined.", self.program.id())
                }
            }
        };

        // Insert the input register.
        register_types.add_input(register.clone(), *register_type)?;

        // Ensure the register type and the input type match.
        if *register_type != register_types.get_type(self, register)? {
            bail!("Input '{register}' does not match the expected input register type.")
        }
        Ok(())
    }

    /// Ensure the given output register is well-formed.
    #[inline]
    fn check_output(
        &self,
        register_types: &RegisterTypes<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Inform the user the output register is an input register, to ensure this is intended behavior.
        if register_types.is_input(register) {
            eprintln!("Output {register} in '{}' is an input register, ensure this is intended", self.program.id());
        }

        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the interface is defined in the program.
                if !self.program.contains_interface(interface_name) {
                    bail!("Interface '{interface_name}' in '{}' is not defined.", self.program.id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !self.program.contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", self.program.id())
                }
            }
            RegisterType::ExternalRecord(locator) => {
                // Ensure the external record type is defined in the program.
                if !self.contains_external_record(locator) {
                    bail!("External record '{locator}' in '{}' is not defined.", self.program.id())
                }
            }
        };

        // Ensure the register type and the output type match.
        if *register_type != register_types.get_type(self, register)? {
            bail!(
                "Output '{register}' does not match the expected output register type: expected '{}', found '{}'",
                register_types.get_type(self, register)?,
                register_type
            )
        }
        Ok(())
    }

    /// Ensures the given instruction is well-formed.
    #[inline]
    fn check_instruction(
        &self,
        register_types: &mut RegisterTypes<N>,
        closure_or_function_name: &Identifier<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        // Ensure the opcode is well-formed.
        self.check_instruction_opcode(register_types, closure_or_function_name, instruction)?;

        // Initialize a vector to store the register types of the operands.
        let mut operand_types = Vec::with_capacity(instruction.operands().len());
        // Iterate over the operands, and retrieve the register type of each operand.
        for operand in instruction.operands() {
            // Retrieve and append the register type.
            operand_types.push(match operand {
                Operand::Literal(literal) => RegisterType::Plaintext(PlaintextType::from(literal.to_type())),
                Operand::Register(register) => register_types.get_type(self, register)?,
            });
        }

        // Compute the destination register types.
        let destination_types = instruction.output_types(self, &operand_types)?;

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
    #[inline]
    fn check_instruction_opcode(
        &self,
        register_types: &RegisterTypes<N>,
        closure_or_function_name: &Identifier<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        match instruction.opcode() {
            Opcode::Literal(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Program::<N>::is_reserved_opcode(opcode), "'{opcode}' is not an opcode.");
                // Ensure the instruction is not the cast operation.
                ensure!(!matches!(instruction, Instruction::Cast(..)), "Instruction '{instruction}' is a 'cast'.");
                // Ensure the instruction has one destination register.
                ensure!(
                    instruction.destinations().len() == 1,
                    "Instruction '{instruction}' has multiple destinations."
                );
            }
            Opcode::Assert(opcode) => {
                // Ensure the instruction belongs to the defined set.
                if !["assert.eq", "assert.neq"].contains(&opcode) {
                    bail!("Instruction '{instruction}' is not the opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                match opcode {
                    "assert.eq" => ensure!(
                        matches!(instruction, Instruction::AssertEq(..)),
                        "Instruction '{instruction}' is not the opcode '{opcode}'."
                    ),
                    "assert.neq" => ensure!(
                        matches!(instruction, Instruction::AssertNeq(..)),
                        "Instruction '{instruction}' is not the opcode '{opcode}'."
                    ),
                    _ => bail!("Instruction '{instruction}' is not the opcode '{opcode}'."),
                }
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
                        if self.program.id() == program_id {
                            bail!("Locator '{locator}' does not reference an external program.");
                        }
                        // Ensure the current program contains an import for this external program.
                        if !self.program.imports().keys().contains(program_id) {
                            bail!("External program '{}' is not imported by '{program_id}'.", locator.program_id());
                        }

                        // Retrieve the program.
                        let external = self.get_external_program(program_id)?;
                        // Ensure the function or closure exists in the program.
                        if !external.contains_function(resource) && !external.contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", external.id())
                        }
                    }
                    CallOperator::Resource(resource) => {
                        // Ensure the resource does not reference this closure or function.
                        if resource == closure_or_function_name {
                            bail!("Cannot invoke 'call' to self (in '{resource}'): self-recursive call.")
                        }

                        // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                        //  But there are legitimate uses for passing a record through to an internal function.
                        //  We could invoke the internal function without a state transition, but need to match visibility.
                        if self.program.contains_function(resource) {
                            bail!(
                                "Cannot call '{resource}' from '{closure_or_function_name}'. Use a closure ('closure {resource}:') instead."
                            )
                        }
                        // Ensure the function or closure exists in the program.
                        // if !self.program.contains_function(resource) && !self.program.contains_closure(resource) {
                        if !self.program.contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", self.program.id())
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
                        if !self.program.contains_interface(interface_name) {
                            bail!("Interface '{interface_name}' is not defined.")
                        }
                        // Retrieve the interface.
                        let interface = self.program.get_interface(interface_name)?;
                        // Ensure the operand types match the interface.
                        register_types.matches_interface(self, instruction.operands(), &interface)?;
                    }
                    RegisterType::Record(record_name) => {
                        // Ensure the record type is defined in the program.
                        if !self.program.contains_record(record_name) {
                            bail!("Record '{record_name}' is not defined.")
                        }
                        // Retrieve the record type.
                        let record_type = self.program.get_record(record_name)?;
                        // Ensure the operand types match the record type.
                        register_types.matches_record(self, instruction.operands(), &record_type)?;
                    }
                    RegisterType::ExternalRecord(_locator) => {
                        bail!("Illegal operation: Cannot cast to an external record.")
                    }
                }
            }
            Opcode::Commit(opcode) => {
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
}
