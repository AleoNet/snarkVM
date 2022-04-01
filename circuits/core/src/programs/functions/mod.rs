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

pub mod input;
pub use input::*;

pub mod instructions;
pub use instructions::*;

pub mod output;
pub use output::*;

mod parsers;

use crate::{
    functions::parsers::*,
    helpers::{Locator, Register},
    Annotation,
    Identifier,
    Value,
};
use snarkvm_circuits_types::prelude::*;

use indexmap::{IndexMap, IndexSet};

pub struct Function<E: Environment> {
    /// The name of the function.
    name: Identifier<E>,
    /// The map of register locators to their values.
    /// When input statements are added, a new entry of `(locator, None)` is added to this map.
    /// When input assignments are added, the entry is updated to `(locator, Some(value))`.
    /// No changes occur to `registers` when output statements are added.
    registers: IndexMap<Locator, Option<Value<E>>>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    input_statements: IndexSet<Input<E>>,
    /// The instructions, in order of execution.
    instructions: Vec<Instruction<E>>,
    /// The output statements, in order of the desired output.
    /// There is no expectation that the output registers are in any ordering.
    output_statements: IndexSet<Output<E>>,
}

impl<E: Environment> Function<E> {
    /// Initializes a new function with the given name.
    pub fn new(name: &str) -> Self {
        Self {
            name: Identifier::from_str(name),
            registers: IndexMap::new(),
            input_statements: IndexSet::new(),
            instructions: Vec::new(),
            output_statements: IndexSet::new(),
        }
    }

    /// Returns the name of the function.
    pub fn name(&self) -> &Identifier<E> {
        &self.name
    }

    /// Adds the input statement into memory.
    /// This method is called before a function is run.
    /// This method is only called before `new_instruction` is ever called.
    /// If the given input annotation is for a template, then the template must be added before this method is called.
    ///
    /// # Errors
    /// This method will halt if there are instructions or output statements in memory already.
    /// This method will halt if the input statement was previously added.
    /// This method will halt if the given input register is not new.
    /// This method will halt if the given input register has a previously saved annotation in memory.
    /// This method will halt if the given inputs are not incrementing monotonically.
    /// This method will halt if the given input annotation references a non-existent template.
    #[inline]
    fn add_input_statement(&mut self, input: Input<E>) {
        // Ensure there are no instructions or output statements in memory.
        if !self.instructions.is_empty() {
            E::halt("Cannot add input statement after instructions have been added")
        } else if !self.output_statements.is_empty() {
            E::halt("Cannot add input statement after output statements have been added")
        }

        // Ensure the input statement was not previously added.
        if self.input_statements.contains(&input) {
            E::halt(format!("Input statement {input} was previously added"))
        }

        // Ensure the input does not exist in the registers.
        let register = input.register();
        if self.registers.contains_key(register.locator()) {
            E::halt(format!("Input register {register} was previously stored"))
        }

        // If the input annotation is a composite, ensure the input is referencing a valid template.
        if let Annotation::Composite(identifier) = input.annotation() {
            if !self.templates.contains_key(identifier) {
                E::halt("Input annotation references non-existent composite template")
            }
        }

        // Ensure the input register is new, and incrementing monotonically.
        // This operation is only performed before the new variables are created,
        // so the performance of this operation should be reasonable.
        let mut index = 0;
        while self.registers.contains_key(&index) {
            index += 1;
        }
        if index != *register.locator() {
            E::halt(format!("Invalid input ordering detected in memory at register {index}"))
        }

        // Insert the input statement to memory.
        self.input_statements.insert(input);
    }

    // TODO (howardwu): Instructions should have annotations, and we should check them here.
    /// Adds the given instruction into memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if there are no input statements in memory.
    /// This method will halt if the given instruction already exists in memory.
    /// This method will halt if the destination register already exists in memory.
    /// This method will halt if the destination register locator does not monotonically increase.
    /// This method will halt if any operand register does not already exist in memory.
    /// This method will halt if any registers are already set.
    #[inline]
    fn add_instruction(&mut self, instruction: Instruction<E>) {
        // Ensure there are input statements in memory.
        if self.input_statements.is_empty() {
            E::halt("Cannot add instruction before input statements have been added")
        }

        // Ensure the instruction does not already exist in memory.
        if self.instructions.contains(&instruction) {
            E::halt(format!("Instruction {instruction} was previously stored"))
        }

        // Ensure the destination register does not exist.
        if self.registers.contains_key(instruction.destination().locator()) {
            E::halt(format!("Destination {} already exists", instruction.destination()))
        }

        // Ensure the destination register locator is monotonically increasing.
        if !self.registers.contains_key(&instruction.destination().locator().saturating_sub(1)) {
            E::halt(format!("Destination {} is not monotonically increasing", instruction.destination()))
        }

        // Ensure the operand registers exist.
        for register in instruction.operands().iter().filter_map(|operand| operand.register()) {
            if !self.registers.contains_key(register.locator()) {
                E::halt(format!("Operand register {register} does not exist"))
            }
        }

        // Ensure the destination register and operand registers are not already set.
        for register in [instruction.destination().clone()]
            .iter()
            .chain(instruction.operands().iter().filter_map(|operand| operand.register()))
        {
            if let Some(Some(..)) = self.registers.get(register.locator()) {
                E::halt(format!("Register {register} is already set"))
            }
        }

        // Add the instruction to the memory.
        self.instructions.push(instruction);
    }

    /// Adds the output statement into memory.
    /// This method is called before a function is run.
    /// If the given output is for a template, then the template must be added before this method is called.
    ///
    /// # Errors
    /// This method will halt if there are no input statements or instructions in memory.
    /// This method will halt if the given output register is new.
    /// This method will halt if the given output register is already set.
    /// This method will halt if the given output annotation references a non-existent template.
    #[inline]
    fn add_output_statement(&mut self, output: Output<E>) {
        // Ensure there are input statements and instructions in memory.
        if self.input_statements.is_empty() || self.instructions.is_empty() {
            E::halt("Cannot add output statement before input statements or instructions have been added")
        }

        // Ensure the output exists in the registers.
        let register = output.register();
        if !self.registers.contains_key(register.locator()) {
            E::halt(format!("Output register {register} is missing"))
        }

        // Ensure the output register is not already set.
        if let Some(Some(..)) = self.registers.get(register.locator()) {
            E::halt(format!("Output register {register} was already set"))
        }

        // If the output annotation is for a composite, ensure the output is referencing a valid template.
        if let Annotation::Composite(identifier) = output.annotation() {
            if !self.templates.contains_key(identifier) {
                E::halt("Output annotation references non-existent composite template")
            }
        }

        // Insert the output statement to memory.
        self.output_statements.insert(output);
    }

    /// Assigns the given input value to the corresponding register in memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if the input registers are not assigned monotonically.
    /// This method will halt if the input register was previously stored.
    /// This method will halt if the register is not an input register.
    /// This method will halt if the input statement does not exist.
    /// This method will halt if the annotation does not match.
    #[inline]
    fn assign_input(&mut self, input: Input<E>, value: Value<E>) {
        // Ensure the input exists in the registers.
        let register = input.register();
        if !self.registers.contains_key(register.locator()) {
            E::halt(format!("Register {register} does not exist"))
        }

        // Ensure the input is an input register.
        if !self.input_statements.contains(&input) {
            E::halt(format!("Register {register} is not an input register"))
        }

        // Ensure the previous input is assigned before the current input.
        match self.registers.get(&register.locator().saturating_sub(1)) {
            Some(None) | None => {
                E::halt(format!("Cannot assign input register {register} as the previous register is not assigned yet"))
            }
            _ => (),
        }

        // If the input annotation is a composite, ensure the input value matches the template.
        if let Annotation::Composite(identifier) = input.annotation() {
            match self.templates.get(identifier) {
                Some(template) => {
                    // TODO (howardwu): Check that it matches expected format.
                    // if !template.matches(&value) {
                    //     E::halt(format!("Input value does not match template {template}"))
                    // }
                }
                None => E::halt("Input annotation references non-existent template"),
            }
        }

        // Assign the input value to the register.
        if let Some(Some(..)) = self.registers.insert(*register.locator(), Some(value)) {
            E::halt(format!("Input register {register} was already assigned"))
        }

        // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
    }

    /// Loads the value of a given operand from memory.
    ///
    /// # Errors
    /// This function will halt if the register locator is not found.
    /// In the case of register members, this function will halt if the member is not found.
    #[inline]
    fn load<O: Into<Operand<E>>>(&self, operand: O) -> Value<E> {
        // Attempt to load the value from the operand.
        let (register, candidate) = match operand.into() {
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => match register {
                // Load the value for a register.
                Register::Locator(locator) => (register, self.registers.get(&locator)),
                // Load the value for a register member.
                Register::Member(locator, _) => (register, self.registers.get(&locator)),
            },
            // If the operand is a value, return the value.
            Operand::Value(value) => return value,
        };

        // Retrieve the value from the option.
        let value = match candidate {
            // Return the value if it exists.
            Some(Some(value)) => value,
            // Halts if the value does not exist.
            Some(None) | None => E::halt(format!("Failed to locate register \'{register}\'")),
        };

        // If the register is a locator, then return the value.
        if let Register::Locator(..) = register {
            (*value).clone()
        }
        // If the register is a register member, then load the specific value.
        else if let Register::Member(_, member_name) = register {
            match value {
                // Halts if the value is not a composite.
                Value::Literal(..) => E::halt("Cannot load a register member from a literal"),
                // Retrieve the value of the member (from the value).
                Value::Composite(identifier, composite) => {
                    // Retrieve the member index of the identifier (from the template).
                    let member_index = match self.templates.get(identifier) {
                        Some(template) => template
                            .members()
                            .iter()
                            .position(|member| member.name() == member_name)
                            .unwrap_or_else(|| E::halt(format!("Failed to locate {member_name} in {identifier}"))),
                        // Halts if the template does not exist.
                        None => E::halt(format!("Failed to locate template for identifier {identifier}")),
                    };
                    // Return the value of the member.
                    match composite.get(member_index) {
                        Some(value) => (*value).clone(),
                        // Halts if the member does not exist.
                        None => E::halt(format!("Failed to locate register {register}")),
                    }
                }
            }
        }
        // Halts if the register is neither a locator nor a register member.
        else {
            E::halt(format!("Failed to locate register {register}"))
        }
    }

    /// Stores the given register and value in memory, assuming the register has not been previously stored.
    ///
    /// # Errors
    /// This function will halt if the register was previously stored.
    #[inline]
    fn store<V: Into<Value<E>>>(&mut self, register: &Register<E>, value: V) {
        // Store the value in the register.
        let previous = match register {
            // Store the value for a register.
            Register::Locator(locator) => self.registers.insert(*locator, Some(value.into())),
            // Store the value for a register member.
            Register::Member(locator, _) => self.registers.insert(*locator, Some(value.into())),
        };

        // Ensure the register has not been previously stored.
        if let Some(Some(..)) = previous {
            E::halt(format!("Register {} was previously stored", register.locator()))
        }
    }
}
