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

use crate::program::{Annotation, Identifier, Program, Sanitizer, Value};
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
    /// This method will halt if any registers are already assigned.
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

        // If the input annotation is a composite, ensure the input is referencing a valid template.
        if let Annotation::Composite(template) = input.annotation() {
            if !P::contains_template(template) {
                P::halt(format!("Input type \'{template}\' does not exist"))
            }
        }

        // Define the input register.
        self.registers.define(register);
        // Insert the input statement.
        self.inputs.insert(input);
    }

    // TODO (howardwu): Instructions should have annotations, and we should check them here.
    /// Adds the given instruction into memory.
    /// This method is called before a function is run.
    ///
    /// # Errors
    /// This method will halt if there are no input statements in memory.
    /// This method will halt if any registers are already assigned.
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

        // Iterate over the operand registers.
        for register in instruction.operands().iter().filter_map(|operand| operand.register()) {
            // Ensure the operand registers are defined.
            if !self.registers.is_defined(register) {
                P::halt(format!("Operand register {register} does not exist"))
            }

            // Ensure the operand registers are not already assigned.
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
    /// This method will halt if any registers are already assigned.
    /// This method will halt if the given output register is new.
    /// This method will halt if the given output register is already set.
    /// This method will halt if the given output annotation references a non-existent template.
    #[inline]
    fn add_output(&mut self, output: Output<P>) {
        // Ensure there are input statements and instructions in memory.
        if self.inputs.is_empty() || self.instructions.is_empty() {
            P::halt("Cannot add output statement before input statements or instructions have been added")
        }

        // Ensure the registers are clean.
        if self.registers.is_dirty() {
            P::halt("Registers cannot contain assignments prior to evaluation")
        }

        // Ensure the output exists in the registers.
        let register = output.register();
        if !self.registers.is_defined(register) {
            P::halt(format!("Output register {register} is missing"))
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
    /// This method will halt if any registers are already assigned.
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    fn evaluate(&mut self, inputs: &[Value<P>]) -> Vec<Value<P>> {
        // Ensure there are input statements and instructions in memory.
        if self.inputs.is_empty() || self.instructions.is_empty() {
            P::halt("Cannot evaluate a function without input statements or instructions")
        }

        // Ensure the function is not already evaluated.
        if self.registers.is_dirty() {
            P::halt("Registers cannot contain assignments prior to evaluation")
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
        // Zip the input statements and input values together.
        for (input, value) in self.inputs.iter().zip_eq(values.iter()) {
            // Ensure the input is an input register.
            let register = input.register();
            if !self.inputs.contains(input) {
                P::halt(format!("Register {register} is not an input register"))
            }

            // If the input annotation is a composite, ensure the input value matches the template.
            if let Annotation::Composite(template_name) = input.annotation() {
                match P::get_template(&template_name) {
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

impl<P: Program> Parser for Function<P> {
    type Environment = P;

    /// Parses a string into a function.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'function' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the function name from the string.
        let (string, name) = Identifier::<P>::parse(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the inputs from the string.
        let (string, inputs) = many1(Input::parse)(string)?;
        // Parse the instructions from the string.
        let (string, instructions) = many1(Instruction::parse)(string)?;
        // Parse the outputs from the string.
        let (string, outputs) = many0(Output::parse)(string)?;

        // Initialize a new function.
        let mut function = Self::new(&name.to_string());
        inputs.into_iter().for_each(|input| function.add_input(input));
        instructions.into_iter().for_each(|instruction| function.add_instruction(instruction));
        outputs.into_iter().for_each(|output| function.add_output(output));

        Ok((string, function))
    }
}

impl<P: Program> TypeName for Function<P> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "function"
    }
}

impl<P: Program> fmt::Display for Function<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut function = format!("{} {}:\n", Self::type_name(), self.name);
        for input in &self.inputs {
            function += &format!("    {}\n", input);
        }
        for instruction in &self.instructions {
            function += &format!("    {}\n", instruction);
        }
        for output in &self.outputs {
            function += &format!("    {}\n", output);
        }
        function.pop(); // trailing newline
        write!(f, "{}", function)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::AleoProgram;

    #[test]
    fn test_function_evaluate() {
        let mut function = Function::<AleoProgram>::from_str(
            r"
function foo:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;",
        );
        let first = Value::<AleoProgram>::from_str("2field.public");
        let second = Value::from_str("3field.private");

        // Run the function.
        let expected = Value::<AleoProgram>::from_str("5field.private");
        let candidate = function.evaluate(&[first.clone(), second.clone()]);
        assert_eq!(expected.to_string(), candidate[0].to_string());

        // Re-run to ensure state continues to work.
        let expected = Value::<AleoProgram>::from_str("5field.private");
        let candidate = function.evaluate(&[first, second]);
        assert_eq!(expected.to_string(), candidate[0].to_string());
    }

    #[test]
    fn test_function_parse() {
        let function = Function::<AleoProgram>::parse(
            r"
function foo:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;
",
        )
        .unwrap()
        .1;
        assert_eq!("foo", function.name().to_string());
        assert_eq!(2, function.inputs.len());
        assert_eq!(1, function.instructions.len());
        assert_eq!(1, function.outputs.len());
    }

    #[test]
    fn test_function_display() {
        let expected = r"function foo:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;";
        let function = Function::<AleoProgram>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{function}"),);
    }
}
