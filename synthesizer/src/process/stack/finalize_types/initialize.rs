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

impl<N: Network> FinalizeTypes<N> {
    /// Initializes a new instance of `FinalizeTypes` for the given finalize.
    /// Checks that the given finalize is well-formed for the given stack.
    #[inline]
    pub(super) fn initialize_finalize_types(stack: &Stack<N>, finalize: &Finalize<N>) -> Result<Self> {
        // Initialize a map of registers to their types.
        let mut finalize_types = Self { inputs: IndexMap::new(), destinations: IndexMap::new() };

        // Step 1. Check the inputs are well-formed.
        for input in finalize.inputs() {
            // Check the input register type.
            finalize_types.check_input(stack, input.register(), &RegisterType::from(*input.finalize_type()))?;
        }

        // Step 2. Check the commands are well-formed.
        for command in finalize.commands() {
            // Check the command opcode, operands, and destinations.
            finalize_types.check_command(stack, finalize.name(), command)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in finalize.outputs() {
            // Retrieve the register type and check the output register type.
            finalize_types.check_output(stack, output.register(), &RegisterType::from(*output.finalize_type()))?;
        }

        Ok(finalize_types)
    }
}

impl<N: Network> FinalizeTypes<N> {
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

impl<N: Network> FinalizeTypes<N> {
    /// Ensure the given input register is well-formed.
    #[inline]
    fn check_input(&mut self, stack: &Stack<N>, register: &Register<N>, register_type: &RegisterType<N>) -> Result<()> {
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
        stack: &Stack<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Inform the user the output register is an input register, to ensure this is intended behavior.
        if self.is_input(register) {
            eprintln!("Output {register} in '{}' is an input register, ensure this is intended", stack.program_id());
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

        // Ensure the register type and the output type match.
        if *register_type != self.get_type(stack, register)? {
            bail!(
                "Output '{register}' does not match the expected output register type: expected '{}', found '{}'",
                self.get_type(stack, register)?,
                register_type
            )
        }
        Ok(())
    }

    /// Ensures the given command is well-formed.
    #[inline]
    fn check_command(&mut self, stack: &Stack<N>, finalize_name: &Identifier<N>, command: &Command<N>) -> Result<()> {
        match command {
            Command::Decrement(decrement) => self.check_decrement(stack, finalize_name, decrement)?,
            Command::Instruction(instruction) => self.check_instruction(stack, finalize_name, instruction)?,
            Command::Increment(increment) => self.check_increment(stack, finalize_name, increment)?,
        }
        Ok(())
    }

    /// Ensures the given decrement command is well-formed.
    #[inline]
    fn check_decrement(&self, stack: &Stack<N>, finalize_name: &Identifier<N>, decrement: &Decrement<N>) -> Result<()> {
        // Ensure the declared mapping in decrement is defined in the program.
        if !stack.program().contains_mapping(decrement.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", decrement.mapping_name(), stack.program_id())
        }

        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, decrement.key())?;
        // Ensure the key is not a record or external record.
        match key_type {
            RegisterType::Plaintext(..) => (),
            RegisterType::Record(..) => bail!("Decrement cannot use a 'record' as a key (found at '{decrement}')"),
            RegisterType::ExternalRecord(..) => {
                bail!("Decrement cannot use an 'external record' as a key (found at '{decrement}')")
            }
        }

        // Retrieve the register type of the value.
        let value_type = self.get_type_from_operand(stack, decrement.value())?;
        // Ensure the decrement value type is a literal that implements the `Add` operation.
        match value_type {
            RegisterType::Plaintext(PlaintextType::Literal(literal_type)) => {
                match literal_type {
                    LiteralType::Address | LiteralType::Boolean | LiteralType::String => {
                        bail!("Decrement cannot decrement by a(n) '{literal_type}' (found at '{decrement}')")
                    }
                    // These literal types are valid for the 'decrement' command.
                    LiteralType::Field
                    | LiteralType::Group
                    | LiteralType::Scalar
                    | LiteralType::I8
                    | LiteralType::I16
                    | LiteralType::I32
                    | LiteralType::I64
                    | LiteralType::I128
                    | LiteralType::U8
                    | LiteralType::U16
                    | LiteralType::U32
                    | LiteralType::U64
                    | LiteralType::U128 => {}
                }
            }
            RegisterType::Plaintext(PlaintextType::Struct(..)) => {
                bail!("Decrement cannot decrement by an 'struct' (found at '{decrement}')")
            }
            RegisterType::Record(..) => bail!("Decrement cannot decrement by a 'record' (found at '{decrement}')"),
            RegisterType::ExternalRecord(..) => {
                bail!("Decrement cannot decrement by an 'external record' (found at '{decrement}')")
            }
        }

        Ok(())
    }

    /// Ensures the given increment command is well-formed.
    #[inline]
    fn check_increment(&self, stack: &Stack<N>, finalize_name: &Identifier<N>, increment: &Increment<N>) -> Result<()> {
        // Ensure the declared mapping in increment is defined in the program.
        if !stack.program().contains_mapping(increment.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", increment.mapping_name(), stack.program_id())
        }

        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, increment.key())?;
        // Ensure the key is not a record or external record.
        match key_type {
            RegisterType::Plaintext(..) => (),
            RegisterType::Record(..) => bail!("Increment cannot use a 'record' as a key (found at '{increment}')"),
            RegisterType::ExternalRecord(..) => {
                bail!("Increment cannot use an 'external record' as a key (found at '{increment}')")
            }
        }

        // Retrieve the register type of the value.
        let value_type = self.get_type_from_operand(stack, increment.value())?;
        // Ensure the increment value type is a literal that implements the `Add` operation.
        match value_type {
            RegisterType::Plaintext(PlaintextType::Literal(literal_type)) => {
                match literal_type {
                    LiteralType::Address | LiteralType::Boolean | LiteralType::String => {
                        bail!("Increment cannot increment by a(n) '{literal_type}' (found at '{increment}')")
                    }
                    // These literal types are valid for the 'increment' command.
                    LiteralType::Field
                    | LiteralType::Group
                    | LiteralType::Scalar
                    | LiteralType::I8
                    | LiteralType::I16
                    | LiteralType::I32
                    | LiteralType::I64
                    | LiteralType::I128
                    | LiteralType::U8
                    | LiteralType::U16
                    | LiteralType::U32
                    | LiteralType::U64
                    | LiteralType::U128 => {}
                }
            }
            RegisterType::Plaintext(PlaintextType::Struct(..)) => {
                bail!("Increment cannot increment by an 'struct' (found at '{increment}')")
            }
            RegisterType::Record(..) => bail!("Increment cannot increment by a 'record' (found at '{increment}')"),
            RegisterType::ExternalRecord(..) => {
                bail!("Increment cannot increment by an 'external record' (found at '{increment}')")
            }
        }

        Ok(())
    }

    /// Ensures the given instruction is well-formed.
    #[inline]
    fn check_instruction(
        &mut self,
        stack: &Stack<N>,
        finalize_name: &Identifier<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        // Ensure the opcode is well-formed.
        self.check_instruction_opcode(stack, finalize_name, instruction)?;

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
        stack: &Stack<N>,
        finalize_name: &Identifier<N>,
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
                bail!("Instruction 'call' is not allowed in 'finalize'");
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
                    RegisterType::Record(..) => {
                        bail!("Unsupported operation: Cannot cast to a record (yet).")
                        // // Ensure the record type is defined in the program.
                        // if !stack.program().contains_record(record_name) {
                        //     bail!("Record '{record_name}' is not defined.")
                        // }
                        // // Retrieve the record type.
                        // let record_type = stack.program().get_record(record_name)?;
                        // // Ensure the operand types match the record type.
                        // self.matches_record(stack, instruction.operands(), &record_type)?;
                    }
                    RegisterType::ExternalRecord(_locator) => {
                        bail!("Illegal operation: Cannot cast to an external record.")
                    }
                }
            }
            Opcode::Command(opcode) => {
                bail!("Fatal error: Cannot check command '{opcode}' as an instruction in 'finalize {finalize_name}'.")
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
            }
            Opcode::Finalize(opcode) => {
                bail!("Forbidden operation: Cannot invoke '{opcode}' in a `finalize` scope.");
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
                    _ => bail!("Instruction '{instruction}' is not for opcode '{opcode}'."),
                }
            }
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
