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
use crate::{
    program::{Branch, Contains, Get, GetOrUse, RandChaCha, Remove, Set, MAX_ADDITIONAL_SEEDS},
    RegisterTypes,
};

impl<N: Network> FinalizeTypes<N> {
    /// Initializes a new instance of `FinalizeTypes` for the given finalize.
    /// Checks that the given finalize is well-formed for the given stack.
    #[inline]
    pub(super) fn initialize_finalize_types(
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize: &Finalize<N>,
    ) -> Result<Self> {
        // Initialize a map of registers to their types.
        let mut finalize_types = Self { inputs: IndexMap::new(), destinations: IndexMap::new() };

        // Step 1. Check the inputs are well-formed.
        for input in finalize.inputs() {
            // Check the input register type.
            finalize_types.check_input(stack, input.register(), input.plaintext_type())?;
        }

        // Step 2. Check the commands are well-formed.
        for command in finalize.commands() {
            // Check the command opcode, operands, and destinations.
            finalize_types.check_command(stack, finalize, command)?;
        }

        Ok(finalize_types)
    }
}

impl<N: Network> FinalizeTypes<N> {
    /// Inserts the given input register and type into the registers.
    /// Note: The given input register must be a `Register::Locator`.
    fn add_input(&mut self, register: Register<N>, plaintext_type: PlaintextType<N>) -> Result<()> {
        // Ensure there are no destination registers set yet.
        ensure!(self.destinations.is_empty(), "Cannot add input registers after destination registers.");

        // Check the input register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                ensure!(self.inputs.len() as u64 == locator, "Register '{register}' is out of order");

                // Insert the input register and type.
                match self.inputs.insert(locator, plaintext_type) {
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
    fn add_destination(&mut self, register: Register<N>, plaintext_type: PlaintextType<N>) -> Result<()> {
        // Check the destination register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                let expected_locator = (self.inputs.len() as u64) + self.destinations.len() as u64;
                ensure!(expected_locator == locator, "Register '{register}' is out of order");

                // Insert the destination register and type.
                match self.destinations.insert(locator, plaintext_type) {
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
    fn check_input(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        register: &Register<N>,
        plaintext_type: &PlaintextType<N>,
    ) -> Result<()> {
        // Ensure the register type is defined in the program.
        match plaintext_type {
            PlaintextType::Literal(..) => (),
            PlaintextType::Struct(struct_name) => {
                // Ensure the struct is defined in the program.
                if !stack.program().contains_struct(struct_name) {
                    bail!("Struct '{struct_name}' in '{}' is not defined.", stack.program_id())
                }
            }
        };

        // Insert the input register.
        self.add_input(register.clone(), *plaintext_type)?;

        // Ensure the register type and the input type match.
        if *plaintext_type != self.get_type(stack, register)? {
            bail!("Input '{register}' does not match the expected input register type.")
        }
        Ok(())
    }

    /// Ensures the given command is well-formed.
    #[inline]
    fn check_command(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize: &Finalize<N>,
        command: &Command<N>,
    ) -> Result<()> {
        match command {
            Command::Instruction(instruction) => self.check_instruction(stack, finalize.name(), instruction)?,
            Command::Contains(contains) => self.check_contains(stack, finalize.name(), contains)?,
            Command::Get(get) => self.check_get(stack, finalize.name(), get)?,
            Command::GetOrUse(get_or_use) => self.check_get_or_use(stack, finalize.name(), get_or_use)?,
            Command::RandChaCha(rand_chacha) => self.check_rand_chacha(stack, finalize.name(), rand_chacha)?,
            Command::Remove(remove) => self.check_remove(stack, finalize.name(), remove)?,
            Command::Set(set) => self.check_set(stack, finalize.name(), set)?,
            Command::BranchEq(branch_eq) => self.check_branch(stack, finalize, branch_eq)?,
            Command::BranchNeq(branch_neq) => self.check_branch(stack, finalize, branch_neq)?,
            // Note that the `Position`s are checked for uniqueness when constructing `Finalize`.
            Command::Position(_) => (),
        }
        Ok(())
    }

    /// Checks that the given variant of the `branch` command is well-formed.
    #[inline]
    fn check_branch<const VARIANT: u8>(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize: &Finalize<N>,
        branch: &Branch<N, VARIANT>,
    ) -> Result<()> {
        // Get the type of the first operand.
        let first_type = self.get_type_from_operand(stack, branch.first())?;
        // Get the type of the second operand.
        let second_type = self.get_type_from_operand(stack, branch.second())?;
        // Check that the operands have the same type.
        ensure!(
            first_type == second_type,
            "Command '{}' expects operands of the same type. Found operands of type '{}' and '{}'",
            Branch::<N, VARIANT>::opcode(),
            first_type,
            second_type
        );
        // Check that the `Position` has been defined.
        ensure!(
            finalize.positions().get(branch.position()).is_some(),
            "Command '{}' expects a defined position to jump to. Found undefined position '{}'",
            Branch::<N, VARIANT>::opcode(),
            branch.position()
        );
        Ok(())
    }

    /// Ensures the given `contains` command is well-formed.
    #[inline]
    fn check_contains(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize_name: &Identifier<N>,
        contains: &Contains<N>,
    ) -> Result<()> {
        // Ensure the declared mapping in `contains` is defined in the program.
        if !stack.program().contains_mapping(contains.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", contains.mapping_name(), stack.program_id())
        }
        // Retrieve the mapping from the program.
        // Note that the unwrap is safe, as we have already checked the mapping exists.
        let mapping = stack.program().get_mapping(contains.mapping_name()).unwrap();
        // Get the mapping key type.
        let mapping_key_type = mapping.key().plaintext_type();
        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, contains.key())?;
        // Check that the key type in the mapping matches the key type in the instruction.
        if *mapping_key_type != key_type {
            bail!(
                "Key type in `contains` '{key_type}' does not match the key type in the mapping '{mapping_key_type}'."
            )
        }
        // Get the destination register.
        let destination = contains.destination().clone();
        // Ensure the destination register is a locator (and does not reference a member).
        ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
        // Insert the destination register.
        self.add_destination(destination, PlaintextType::Literal(LiteralType::Boolean))?;
        Ok(())
    }

    /// Ensures the given `get` command is well-formed.
    #[inline]
    fn check_get(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize_name: &Identifier<N>,
        get: &Get<N>,
    ) -> Result<()> {
        // Ensure the declared mapping in `get` is defined in the program.
        if !stack.program().contains_mapping(get.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", get.mapping_name(), stack.program_id())
        }
        // Retrieve the mapping from the program.
        // Note that the unwrap is safe, as we have already checked the mapping exists.
        let mapping = stack.program().get_mapping(get.mapping_name()).unwrap();
        // Get the mapping key type.
        let mapping_key_type = mapping.key().plaintext_type();
        // Get the mapping value type.
        let mapping_value_type = mapping.value().plaintext_type();
        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, get.key())?;
        // Check that the key type in the mapping matches the key type in the instruction.
        if *mapping_key_type != key_type {
            bail!("Key type in `get` '{key_type}' does not match the key type in the mapping '{mapping_key_type}'.")
        }
        // Get the destination register.
        let destination = get.destination().clone();
        // Ensure the destination register is a locator (and does not reference a member).
        ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
        // Insert the destination register.
        self.add_destination(destination, *mapping_value_type)?;
        Ok(())
    }

    /// Ensures the given `get.or_use` command is well-formed.
    #[inline]
    fn check_get_or_use(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize_name: &Identifier<N>,
        get_or_use: &GetOrUse<N>,
    ) -> Result<()> {
        // Ensure the declared mapping in `get.or_use` is defined in the program.
        if !stack.program().contains_mapping(get_or_use.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", get_or_use.mapping_name(), stack.program_id())
        }
        // Retrieve the mapping from the program.
        // Note that the unwrap is safe, as we have already checked the mapping exists.
        let mapping = stack.program().get_mapping(get_or_use.mapping_name()).unwrap();
        // Get the mapping key type.
        let mapping_key_type = mapping.key().plaintext_type();
        // Get the mapping value type.
        let mapping_value_type = mapping.value().plaintext_type();
        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, get_or_use.key())?;
        // Check that the key type in the mapping matches the key type.
        if *mapping_key_type != key_type {
            bail!(
                "Key type in `get.or_use` '{key_type}' does not match the key type in the mapping '{mapping_key_type}'."
            )
        }
        // Retrieve the register type of the default value.
        let default_value_type = self.get_type_from_operand(stack, get_or_use.default())?;
        // Check that the value type in the mapping matches the default value type.
        if *mapping_value_type != default_value_type {
            bail!(
                "Default value type in `get.or_use` '{default_value_type}' does not match the value type in the mapping '{mapping_value_type}'."
            )
        }
        // Get the destination register.
        let destination = get_or_use.destination().clone();
        // Ensure the destination register is a locator (and does not reference a member).
        ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
        // Insert the destination register.
        self.add_destination(destination, *mapping_value_type)?;
        Ok(())
    }

    /// Ensure the given `rand.chacha` command is well-formed.
    #[inline]
    fn check_rand_chacha(
        &mut self,
        _stack: &(impl StackMatches<N> + StackProgram<N>),
        _finalize_name: &Identifier<N>,
        rand_chacha: &RandChaCha<N>,
    ) -> Result<()> {
        // Ensure the number of operands is within bounds.
        if rand_chacha.operands().len() > MAX_ADDITIONAL_SEEDS {
            bail!("The number of operands must be <= {MAX_ADDITIONAL_SEEDS}")
        }

        // Get the destination register.
        let destination = rand_chacha.destination().clone();
        // Ensure the destination register is a locator (and does not reference a member).
        ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");

        // Get the destination type.
        let destination_type = rand_chacha.destination_type();
        // Ensure the destination type is allowed.
        ensure!(
            !matches!(destination_type, LiteralType::String),
            "Destination type '{destination_type}' is not allowed."
        );

        // Insert the destination register.
        self.add_destination(destination, PlaintextType::from(destination_type))?;
        Ok(())
    }

    /// Ensures the given `set` command is well-formed.
    #[inline]
    fn check_set(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize_name: &Identifier<N>,
        set: &Set<N>,
    ) -> Result<()> {
        // Ensure the declared mapping in `set` is defined in the program.
        if !stack.program().contains_mapping(set.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", set.mapping_name(), stack.program_id())
        }
        // Retrieve the mapping from the program.
        // Note that the unwrap is safe, as we have already checked the mapping exists.
        let mapping = stack.program().get_mapping(set.mapping_name()).unwrap();
        // Get the mapping key type.
        let mapping_key_type = mapping.key().plaintext_type();
        // Get the mapping value type.
        let mapping_value_type = mapping.value().plaintext_type();
        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, set.key())?;
        // Check that the key type in the mapping matches the key type.
        if *mapping_key_type != key_type {
            bail!("Key type in `set` '{key_type}' does not match the key type in the mapping '{mapping_key_type}'.")
        }
        // Retrieve the type of the value.
        let value_type = self.get_type_from_operand(stack, set.value())?;
        // Check that the value type in the mapping matches the type of the value.
        if *mapping_value_type != value_type {
            bail!(
                "Value type in `set` '{value_type}' does not match the value type in the mapping '{mapping_value_type}'."
            )
        }
        Ok(())
    }

    /// Ensures the given `remove` command is well-formed.
    #[inline]
    fn check_remove(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        finalize_name: &Identifier<N>,
        remove: &Remove<N>,
    ) -> Result<()> {
        // Ensure the declared mapping in `remove` is defined in the program.
        if !stack.program().contains_mapping(remove.mapping_name()) {
            bail!("Mapping '{}' in '{}/{finalize_name}' is not defined.", remove.mapping_name(), stack.program_id())
        }
        // Retrieve the mapping from the program.
        // Note that the unwrap is safe, as we have already checked the mapping exists.
        let mapping = stack.program().get_mapping(remove.mapping_name()).unwrap();
        // Get the mapping key type.
        let mapping_key_type = mapping.key().plaintext_type();
        // Retrieve the register type of the key.
        let key_type = self.get_type_from_operand(stack, remove.key())?;
        // Check that the key type in the mapping matches the key type.
        if *mapping_key_type != key_type {
            bail!("Key type in `remove` '{key_type}' does not match the key type in the mapping '{mapping_key_type}'.")
        }
        Ok(())
    }

    /// Ensures the given instruction is well-formed.
    #[inline]
    fn check_instruction(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
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
            operand_types.push(RegisterType::Plaintext(self.get_type_from_operand(stack, operand)?));
        }

        // Compute the destination register types.
        let destination_types = instruction.output_types(stack, &operand_types)?;

        // Insert the destination register.
        for (destination, destination_type) in
            instruction.destinations().into_iter().zip_eq(destination_types.into_iter())
        {
            // Ensure the destination register is a locator (and does not reference a member).
            ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
            // Ensure that the destination type is a plaintext type.
            let destination_type = match destination_type {
                RegisterType::Plaintext(destination_type) => destination_type,
                _ => bail!("Destination type '{destination_type}' must be a plaintext type."),
            };
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
                    RegisterType::Record(..) => {
                        bail!("Illegal operation: Cannot cast to a record.")
                    }
                    RegisterType::ExternalRecord(_locator) => {
                        bail!("Illegal operation: Cannot cast to an external record.")
                    }
                }
            }
            Opcode::Command(opcode) => {
                bail!("Fatal error: Cannot check command '{opcode}' as an instruction in 'finalize {finalize_name}'.")
            }
            Opcode::Commit(opcode) => RegisterTypes::check_commit_opcode(opcode, instruction)?,
            Opcode::Finalize(opcode) => {
                bail!("Forbidden operation: Cannot invoke '{opcode}' in a `finalize` scope.");
            }
            Opcode::Hash(opcode) => RegisterTypes::check_hash_opcode(opcode, instruction)?,
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
