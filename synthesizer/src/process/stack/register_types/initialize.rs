// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> RegisterTypes<N> {
    /// Initializes a new instance of `RegisterTypes` for the given closure.
    /// Checks that the given closure is well-formed for the given stack.
    #[inline]
    pub(super) fn initialize_closure_types(
        stack: &(impl StackMatches<N> + StackProgram<N>),
        closure: &Closure<N>,
    ) -> Result<Self> {
        // Initialize a map of registers to their types.
        let mut register_types = Self { inputs: IndexMap::new(), destinations: IndexMap::new() };

        // Step 1. Check the inputs are well-formed.
        for input in closure.inputs() {
            // Check the input register type.
            register_types.check_input(stack, input.register(), input.register_type())?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in closure.instructions() {
            // Ensure the closure contains no call instructions.
            ensure!(instruction.opcode() != Opcode::Call, "A 'call' instruction is not allowed in closures");
            // Check the instruction opcode, operands, and destinations.
            register_types.check_instruction(stack, closure.name(), instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in closure.outputs() {
            // Ensure the closure output register is not a record.
            ensure!(
                !matches!(output.register_type(), RegisterType::Record(..)),
                "Closure outputs do not support records"
            );

            // Check the output operand type.
            register_types.check_output(stack, output.operand(), output.register_type())?;
        }

        Ok(register_types)
    }

    /// Initializes a new instance of `RegisterTypes` for the given function.
    /// Checks that the given function is well-formed for the given stack.
    #[inline]
    pub(super) fn initialize_function_types(
        stack: &(impl StackMatches<N> + StackProgram<N>),
        function: &Function<N>,
    ) -> Result<Self> {
        // Initialize a map of registers to their types.
        let mut register_types = Self { inputs: IndexMap::new(), destinations: IndexMap::new() };

        // Step 1. Check the inputs are well-formed.
        for input in function.inputs() {
            // TODO (howardwu): In order to support constant inputs, update `Self::deploy()` to allow
            //  the caller to provide optional constant inputs (instead of sampling random constants).
            //  Then, this check can be removed to enable support for constant inputs in functions.
            ensure!(!matches!(input.value_type(), ValueType::Constant(..)), "Constant inputs are not supported");

            // Check the input register type.
            register_types.check_input(stack, input.register(), &RegisterType::from(*input.value_type()))?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in function.instructions() {
            // Check the instruction opcode, operands, and destinations.
            register_types.check_instruction(stack, function.name(), instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in function.outputs() {
            // Check the output operand type.
            register_types.check_output(stack, output.operand(), &RegisterType::from(*output.value_type()))?;
        }

        // Step 4. If the function has a finalize command, check that its operands are all defined.
        if let Some((command, _)) = function.finalize() {
            // Ensure the number of finalize operands is within bounds.
            ensure!(
                command.operands().len() <= N::MAX_INPUTS,
                "Function '{}' has too many finalize operands",
                function.name()
            );

            // Check the type of each finalize operand.
            for operand in command.operands() {
                // Retrieve the register type from the operand.
                let register_type = register_types.get_type_from_operand(stack, operand)?;
                // Ensure the register type is a literal or a struct.
                // See `Stack::execute_function()` for the same set of checks.
                match register_type {
                    RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
                    RegisterType::Plaintext(PlaintextType::Struct(..)) => (),
                    RegisterType::Record(..) => {
                        bail!(
                            "'{}/{}' attempts to pass a 'record' into 'finalize'",
                            stack.program_id(),
                            function.name()
                        );
                    }
                    RegisterType::ExternalRecord(..) => {
                        bail!(
                            "'{}/{}' attempts to pass an 'external record' into 'finalize'",
                            stack.program_id(),
                            function.name()
                        );
                    }
                }
            }
        }

        Ok(register_types)
    }
}

impl<N: Network> RegisterTypes<N> {
    /// Inserts the given input register and type into the registers.
    /// Note: The given input register must be a `Register::Locator`.
    fn add_input(&mut self, register: Register<N>, register_type: RegisterType<N>) -> Result<()> {
        // Ensure there are no destination registers set yet.
        ensure!(self.destinations.is_empty(), "Cannot add input registers after destination registers.");

        // Check the input register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                ensure!(self.inputs.len() as u64 == locator, "Register '{register}' is out of order");

                // Insert the input register and type.
                match self.inputs.insert(locator, register_type) {
                    // If the register already exists, throw an error.
                    Some(..) => bail!("Input '{register}' already exists"),
                    // If the register does not exist, return success.
                    None => Ok(()),
                }
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
    }

    /// Inserts the given destination register and type into the registers.
    /// Note: The given destination register must be a `Register::Locator`.
    fn add_destination(&mut self, register: Register<N>, register_type: RegisterType<N>) -> Result<()> {
        // Check the destination register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                let expected_locator = (self.inputs.len() as u64) + self.destinations.len() as u64;
                ensure!(expected_locator == locator, "Register '{register}' is out of order");

                // Insert the destination register and type.
                match self.destinations.insert(locator, register_type) {
                    // If the register already exists, throw an error.
                    Some(..) => bail!("Destination '{register}' already exists"),
                    // If the register does not exist, return success.
                    None => Ok(()),
                }
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
    }
}

impl<N: Network> RegisterTypes<N> {
    /// Ensure the given input register is well-formed.
    #[inline]
    fn check_input(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                // Ensure the struct is defined in the program.
                if !stack.program().contains_struct(struct_name) {
                    bail!("Struct '{struct_name}' in '{}' is not defined.", stack.program_id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !stack.program().contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", stack.program_id())
                }
            }
            RegisterType::ExternalRecord(locator) => {
                // Ensure the external record type is defined in the program.
                if !stack.contains_external_record(locator) {
                    bail!("External record '{locator}' in '{}' is not defined.", stack.program_id())
                }
            }
        };

        // Insert the input register.
        self.add_input(register.clone(), *register_type)?;

        // Ensure the register type and the input type match.
        if *register_type != self.get_type(stack, register)? {
            bail!("Input '{register}' does not match the expected input register type.")
        }
        Ok(())
    }

    /// Ensure the given output register is well-formed.
    #[inline]
    fn check_output(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        operand: &Operand<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        match operand {
            // Inform the user the output operand is an input register, to ensure this is intended behavior.
            Operand::Register(register) if self.is_input(register) => {
                eprintln!("Output {operand} in '{}' is an input register, ensure this is intended", stack.program_id())
            }
            // Inform the user the output operand is a literal, to ensure this is intended behavior.
            Operand::Literal(..) => {
                eprintln!("Output {operand} in '{}' is a literal, ensure this is intended", stack.program_id())
            }
            // Otherwise, do nothing.
            _ => (),
        }

        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                // Ensure the struct is defined in the program.
                if !stack.program().contains_struct(struct_name) {
                    bail!("Struct '{struct_name}' in '{}' is not defined.", stack.program_id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !stack.program().contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", stack.program_id())
                }
            }
            RegisterType::ExternalRecord(locator) => {
                // Ensure the external record type is defined in the program.
                if !stack.contains_external_record(locator) {
                    bail!("External record '{locator}' in '{}' is not defined.", stack.program_id())
                }
            }
        };

        // Ensure the operand type and the output type match.
        if *register_type != self.get_type_from_operand(stack, operand)? {
            bail!(
                "Output '{operand}' does not match the expected output operand type: expected '{}', found '{}'",
                self.get_type_from_operand(stack, operand)?,
                register_type
            )
        }
        Ok(())
    }

    /// Ensures the given instruction is well-formed.
    #[inline]
    fn check_instruction(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        closure_or_function_name: &Identifier<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        // Ensure the opcode is well-formed.
        self.check_instruction_opcode(stack, closure_or_function_name, instruction)?;

        // Initialize a vector to store the register types of the operands.
        let mut operand_types = Vec::with_capacity(instruction.operands().len());
        // Iterate over the operands, and retrieve the register type of each operand.
        for operand in instruction.operands() {
            // Retrieve and append the register type.
            operand_types.push(self.get_type_from_operand(stack, operand)?);
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
            self.add_destination(destination, destination_type)?;
        }
        Ok(())
    }

    /// Ensures the opcode is a valid opcode and corresponds to the correct instruction.
    /// This method is called when adding a new closure or function to the program.
    #[inline]
    fn check_instruction_opcode(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
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
                    bail!("Instruction '{instruction}' is not for opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                match opcode {
                    "assert.eq" => ensure!(
                        matches!(instruction, Instruction::AssertEq(..)),
                        "Instruction '{instruction}' is not for opcode '{opcode}'."
                    ),
                    "assert.neq" => ensure!(
                        matches!(instruction, Instruction::AssertNeq(..)),
                        "Instruction '{instruction}' is not for opcode '{opcode}'."
                    ),
                    _ => bail!("Instruction '{instruction}' is not for opcode '{opcode}'."),
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
                        if stack.program_id() == program_id {
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
                            bail!("Cannot invoke 'call' to self (in '{resource}'): self-recursive call.")
                        }

                        // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                        //  But there are legitimate uses for passing a record through to an internal function.
                        //  We could invoke the internal function without a state transition, but need to match visibility.
                        if stack.program().contains_function(resource) {
                            bail!(
                                "Cannot call '{resource}' from '{closure_or_function_name}'. Use a closure ('closure {resource}:') instead."
                            )
                        }
                        // Ensure the function or closure exists in the program.
                        // if !self.program.contains_function(resource) && !self.program.contains_closure(resource) {
                        if !stack.program().contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", stack.program_id())
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
                        ensure!(instruction.operands().len() == 1, "Expected 1 operand.");
                    }
                    RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                        // Ensure the struct name exists in the program.
                        if !stack.program().contains_struct(struct_name) {
                            bail!("Struct '{struct_name}' is not defined.")
                        }
                        // Retrieve the struct.
                        let struct_ = stack.program().get_struct(struct_name)?;
                        // Ensure the operand types match the struct.
                        self.matches_struct(stack, instruction.operands(), &struct_)?;
                    }
                    RegisterType::Record(record_name) => {
                        // Ensure the record type is defined in the program.
                        if !stack.program().contains_record(record_name) {
                            bail!("Record '{record_name}' is not defined.")
                        }
                        // Retrieve the record type.
                        let record_type = stack.program().get_record(record_name)?;
                        // Ensure the operand types match the record type.
                        self.matches_record(stack, instruction.operands(), &record_type)?;
                    }
                    RegisterType::ExternalRecord(_locator) => {
                        bail!("Illegal operation: Cannot cast to an external record.")
                    }
                }
            }
            Opcode::Command(opcode) => {
                bail!("Forbidden operation: Instruction '{instruction}' cannot invoke command '{opcode}'.");
            }
            Opcode::Commit(opcode) => Self::check_commit_opcode(opcode, instruction)?,
            Opcode::Finalize(opcode) => {
                bail!("Forbidden operation: Instruction '{instruction}' cannot invoke command '{opcode}'.");
                // // Ensure the opcode is correct.
                // if opcode != "finalize" {
                //     bail!("Instruction '{instruction}' is not for opcode '{opcode}'.");
                // }
            }
            Opcode::Hash(opcode) => Self::check_hash_opcode(opcode, instruction)?,
            Opcode::Is(opcode) => {
                // Ensure the instruction belongs to the defined set.
                if !["is.eq", "is.neq"].contains(&opcode) {
                    bail!("Instruction '{instruction}' is not for opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                match opcode {
                    "is.eq" => ensure!(
                        matches!(instruction, Instruction::IsEq(..)),
                        "Instruction '{instruction}' is not for opcode '{opcode}'."
                    ),
                    "is.neq" => ensure!(
                        matches!(instruction, Instruction::IsNeq(..)),
                        "Instruction '{instruction}' is not for opcode '{opcode}'."
                    ),
                    _ => bail!("Instruction '{instruction}' is not for opcode '{opcode}'."),
                }
            }
        }
        Ok(())
    }
}

impl<N: Network> RegisterTypes<N> {
    /// Ensures the opcode is a valid opcode and corresponds to the `commit` instruction.
    #[inline]
    pub(crate) fn check_commit_opcode(opcode: &str, instruction: &Instruction<N>) -> Result<()> {
        // Ensure the instruction belongs to the defined set.
        if !["commit.bhp256", "commit.bhp512", "commit.bhp768", "commit.bhp1024", "commit.ped64", "commit.ped128"]
            .contains(&opcode)
        {
            bail!("Instruction '{instruction}' is not for opcode '{opcode}'.");
        }
        // Ensure the instruction is the correct one.
        match opcode {
            "commit.bhp256" => ensure!(
                matches!(instruction, Instruction::CommitBHP256(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "commit.bhp512" => ensure!(
                matches!(instruction, Instruction::CommitBHP512(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "commit.bhp768" => ensure!(
                matches!(instruction, Instruction::CommitBHP768(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "commit.bhp1024" => ensure!(
                matches!(instruction, Instruction::CommitBHP1024(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "commit.ped64" => ensure!(
                matches!(instruction, Instruction::CommitPED64(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "commit.ped128" => ensure!(
                matches!(instruction, Instruction::CommitPED128(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            _ => bail!("Instruction '{instruction}' is not for opcode '{opcode}'."),
        }
        Ok(())
    }

    /// Ensures the opcode is a valid opcode and corresponds to the `hash` instruction.
    #[inline]
    pub(crate) fn check_hash_opcode(opcode: &str, instruction: &Instruction<N>) -> Result<()> {
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
            "hash_many.psd2",
            "hash_many.psd4",
            "hash_many.psd8",
        ]
        .contains(&opcode)
        {
            bail!("Instruction '{instruction}' is not for opcode '{opcode}'.");
        }
        // Ensure the instruction is the correct one.
        match opcode {
            "hash.bhp256" => ensure!(
                matches!(instruction, Instruction::HashBHP256(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.bhp512" => ensure!(
                matches!(instruction, Instruction::HashBHP512(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.bhp768" => ensure!(
                matches!(instruction, Instruction::HashBHP768(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.bhp1024" => ensure!(
                matches!(instruction, Instruction::HashBHP1024(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.ped64" => ensure!(
                matches!(instruction, Instruction::HashPED64(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.ped128" => ensure!(
                matches!(instruction, Instruction::HashPED128(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.psd2" => ensure!(
                matches!(instruction, Instruction::HashPSD2(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.psd4" => ensure!(
                matches!(instruction, Instruction::HashPSD4(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash.psd8" => ensure!(
                matches!(instruction, Instruction::HashPSD8(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash_many.psd2" => ensure!(
                matches!(instruction, Instruction::HashManyPSD2(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash_many.psd4" => ensure!(
                matches!(instruction, Instruction::HashManyPSD4(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            "hash_many.psd8" => ensure!(
                matches!(instruction, Instruction::HashManyPSD8(..)),
                "Instruction '{instruction}' is not for opcode '{opcode}'."
            ),
            _ => bail!("Instruction '{instruction}' is not for opcode '{opcode}'."),
        }
        Ok(())
    }
}
