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

mod input;
use input::*;

pub mod instructions;
pub use instructions::*;

mod output;
use output::*;

mod registers;
use registers::*;

mod parsers;

use crate::{Annotation, Identifier, Program, Value};
use snarkvm_circuits_types::prelude::*;

use indexmap::IndexSet;

pub struct Function<P: Program> {
    /// The name of the function.
    name: Identifier<P>,
    /// The map of register locators to their values.
    /// When input statements are added, a new entry of `(locator, None)` is added to this map.
    /// When input assignments are added, the entry is updated to `(locator, Some(value))`.
    /// No changes occur to `registers` when output statements are added.
    registers: Registers<P>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    inputs: IndexSet<Input<P>>,
    /// The instructions, in order of execution.
    instructions: Vec<Instruction<P>>,
    /// The output statements, in order of the desired output.
    /// There is no expectation that the output registers are in any ordering.
    outputs: IndexSet<Output<P>>,
}

impl<P: Program> Function<P> {
    /// Initializes a new function with the given name.
    pub fn new(name: &str) -> Self {
        Self {
            name: Identifier::from_str(name),
            registers: Registers::new(),
            inputs: IndexSet::new(),
            instructions: Vec::new(),
            outputs: IndexSet::new(),
        }
    }

    /// Returns the name of the function.
    pub fn name(&self) -> &Identifier<P> {
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
    fn add_input(&mut self, input: Input<P>) {
        // Ensure there are no instructions or output statements in memory.
        if !self.instructions.is_empty() {
            P::halt("Cannot add inputs after instructions have been added")
        } else if !self.outputs.is_empty() {
            P::halt("Cannot add inputs after outputs have been added")
        }

        // Ensure the input statement was not previously added.
        let register = input.register();
        if self.inputs.contains(&input) {
            P::halt(format!("Input \'{register}\' was previously added"))
        }

        // Ensure the input does not exist in the registers.
        if self.registers.is_defined(register) {
            P::halt(format!("Input \'{register}\' was previously stored"))
        }

        // If the input annotation is a composite, ensure the input is referencing a valid template.
        if let Annotation::Composite(template) = input.annotation() {
            if !P::contains_template(template) {
                P::halt(format!("Input type \'{template}\' does not exist"))
            }
        }

        // Define the input register.
        self.registers.define(input.register());
        // Insert the input statement.
        self.inputs.insert(input);
    }

    // TODO (howardwu): Instructions should have annotations, and we should check them here.
    /// Adds the given instruction into memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if there are no input statements in memory.
    /// This method will halt if the destination register already exists in memory.
    /// This method will halt if the destination register locator does not monotonically increase.
    /// This method will halt if any operand register does not already exist in memory.
    /// This method will halt if any registers are already set.
    #[inline]
    fn add_instruction(&mut self, instruction: Instruction<P>) {
        // Ensure there are input statements in memory.
        if self.inputs.is_empty() {
            P::halt("Cannot add instruction before input statements have been added")
        }

        // Ensure the destination register does not exist.
        if self.registers.is_defined(instruction.destination()) {
            P::halt(format!("Destination {} already exists", instruction.destination()))
        }

        // Ensure the operand registers exist.
        for register in instruction.operands().iter().filter_map(|operand| operand.register()) {
            if !self.registers.is_defined(register) {
                P::halt(format!("Operand register {register} does not exist"))
            }
        }

        // Ensure the destination register and operand registers are not already assigned.
        for register in [instruction.destination().clone()]
            .iter()
            .chain(instruction.operands().iter().filter_map(|operand| operand.register()))
        {
            if self.registers.is_assigned(register) {
                P::halt(format!("Register {register} is already assigned"))
            }
        }

        // Define the destination register.
        self.registers.define(instruction.destination());
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
    fn add_output(&mut self, output: Output<P>) {
        // Ensure there are input statements and instructions in memory.
        if self.inputs.is_empty() || self.instructions.is_empty() {
            P::halt("Cannot add output statement before input statements or instructions have been added")
        }

        // Ensure the output exists in the registers.
        let register = output.register();
        if !self.registers.is_defined(register) {
            P::halt(format!("Output register {register} is missing"))
        }

        // Ensure the output register is not already assigned.
        if self.registers.is_assigned(register) {
            P::halt(format!("Output register {register} was already assigned"))
        }

        // If the output annotation is for a composite, ensure the output is referencing a valid template.
        if let Annotation::Composite(identifier) = output.annotation() {
            if !P::contains_template(identifier) {
                P::halt("Output annotation references non-existent composite template")
            }
        }

        // Insert the output statement to memory.
        self.outputs.insert(output);
    }

    /// Evaluates the function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if there are no input statements or instructions in memory.
    /// This method will halt if there are any registers that are assigned.
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    fn evaluate(&mut self, inputs: &[Value<P>]) -> Vec<Value<P>> {
        // Ensure there are input statements and instructions in memory.
        if self.inputs.is_empty() || self.instructions.is_empty() {
            P::halt("Cannot evaluate a function without input statements or instructions")
        }

        // Ensure the function is not already evaluated.
        if self.registers.is_dirty() {
            P::halt("Function is already evaluated and needs to be cleared")
        }

        // Ensure the number of inputs matches the number of input statements.
        if self.inputs.len() != inputs.len() {
            P::halt(format!("Expected {} inputs, but given {}", self.inputs.len(), inputs.len()))
        }

        // Assign the inputs and ensure they matches the input statements.
        self.assign_inputs(inputs);

        // Evaluate the instructions.
        for instruction in self.instructions.iter() {
            instruction.evaluate(&mut self.registers);
        }

        // Load the outputs.
        let mut outputs = Vec::with_capacity(self.outputs.len());
        for output in self.outputs.iter() {
            outputs.push(self.registers.load(output.register()));
        }

        // Clear the register assignments.
        self.registers.clear();

        outputs
    }
}

impl<P: Program> Function<P> {
    /// Assigns the given input values to the corresponding registers in memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if the input registers are not assigned monotonically.
    /// This method will halt if the input register was previously stored.
    /// This method will halt if the register is not an input register.
    /// This method will halt if the input statement does not exist.
    /// This method will halt if the annotation does not match.
    #[inline]
    fn assign_inputs(&mut self, values: &[Value<P>]) {
        for (input, value) in self.inputs.iter().zip_eq(values.iter()) {
            // Ensure the input exists in the registers.
            let register = input.register();
            if !self.registers.is_defined(register) {
                P::halt(format!("Register {register} does not exist"))
            }

            // Ensure the input is an input register.
            if !self.inputs.contains(input) {
                P::halt(format!("Register {register} is not an input register"))
            }

            // If the input annotation is a composite, ensure the input value matches the template.
            if let Annotation::Composite(identifier) = input.annotation() {
                match P::get_template(identifier) {
                    Some(template) => {
                        // TODO (howardwu): Check that it matches expected format.
                        // if !template.matches(&value) {
                        //     P::halt(format!("Input value does not match template {template}"))
                        // }
                    }
                    None => P::halt("Input annotation references non-existent template"),
                }
            }

            // Assign the input value to the register.
            // This call will halt if the register is a register member, or if the register is already assigned.
            self.registers.assign(register, value.clone());

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
        }
    }
}
