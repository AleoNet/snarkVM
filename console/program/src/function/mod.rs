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

mod operand;
use operand::*;

mod output;
use output::*;

mod register;
pub use register::Register;

pub struct Function;

// use crate::{Annotation, Identifier, Input, Output, Program, Sanitizer, Value};
// use snarkvm_console_network::prelude::*;
// use snarkvm_utilities::{
//     error,
//     io::{Read, Result as IoResult, Write},
//     FromBytes,
//     ToBytes,
// };
//
// use indexmap::{IndexMap, IndexSet};
// use std::{cell::RefCell, rc::Rc};
//
// pub trait Opcode {}
//
// pub enum Instruction<N: Network, O: Opcode> {
//     Unary { operand: Operand<N> },
// }
//
// impl<N: Network, O: Opcode> Instruction<N, O> {}
//
// enum RegisterType {
//     Input,
//     Destination,
// }
//
// #[derive(Clone)]
// pub struct Function<N: Network> {
//     /// The name of the function.
//     name: Identifier<N>,
//     // /// The map of register locators to their values.
//     // /// When input statements are added, a new entry of `(locator, None)` is added to this map.
//     // /// When input assignments are added, the entry is updated to `(locator, Some(value))`.
//     // /// No changes occur to `registers` when output statements are added.
//     // registers: Registers<N>,
//     registers: IndexMap<u64, RegisterType>,
//     /// The input statements, added in order of the input registers.
//     /// Input assignments are ensured to match the ordering of the input statements.
//     inputs: IndexSet<Input<N>>,
//     /// The instructions, in order of execution.
//     instructions: Vec<Instruction<N>>,
//     /// The output statements, in order of the desired output.
//     /// There is no expectation that the output registers are in any ordering.
//     outputs: IndexSet<Output<N>>,
// }
//
// impl<N: Network> Function<N> {
//     /// Initializes a new function with the given name.
//     pub fn new(name: &str) -> Self {
//         Self {
//             name: Identifier::from_str(name),
//             registers: Registers::new(),
//             inputs: IndexSet::new(),
//             instructions: Vec::new(),
//             outputs: IndexSet::new(),
//         }
//     }
//
//     /// Returns the name of the function.
//     pub fn name(&self) -> &Identifier<N> {
//         &self.name
//     }
//
//     /// Adds the input statement to the function.
//     /// This method is called before a function is run.
//     /// This method is only called before `new_instruction` is ever called.
//     /// If the given input annotation is for a definition, then the definition must be added before this method is called.
//     ///
//     /// # Errors
//     /// This method will halt if there are instructions or output statements in memory already.
//     /// This method will halt if the maximum number of inputs has been reached.
//     /// This method will halt if any registers are already assigned.
//     /// This method will halt if the input statement was previously added.
//     /// This method will halt if the given input register is not new.
//     /// This method will halt if the given input register has a previously saved annotation in memory.
//     /// This method will halt if the given inputs are not incrementing monotonically.
//     /// This method will halt if the given input annotation references a non-existent definition.
//     #[inline]
//     pub fn add_input(&mut self, input: Input<N>) -> Result<()> {
//         // Ensure there are no instructions or output statements in memory.
//         ensure!(self.instructions.is_empty(), "Cannot add inputs after instructions have been added");
//         ensure!(self.outputs.is_empty(), "Cannot add inputs after outputs have been added");
//
//         // Ensure the maximum number of inputs has not been exceeded.
//         ensure!(self.inputs.len() <= N::MAX_INPUTS, "Cannot add more than {} inputs", N::MAX_INPUTS);
//         // Ensure the input statement was not previously added.
//         ensure!(!self.inputs.contains(&input), "Cannot add duplicate input statement");
//
//         // Retrieve the input register.
//         let register = input.register();
//         // Ensure the input register is a locator (and does not reference a member).
//         ensure!(register.is_locator(), "Input registers must be locators and cannot reference members");
//         // Ensure the input register is new.
//         ensure!(!self.registers.contains_key(&register), "Input register {register} already exists");
//
//         // // If the input annotation is a definition, ensure the input is referencing a valid definition.
//         // if let Annotation::Definition(definition) = input.value_type() {
//         //     if !P::contains_definition(definition) {
//         //         P::halt(format!("Input type \'{definition}\' does not exist"))
//         //     }
//         // }
//
//         // Insert the input register.
//         self.registers.insert(register, RegisterType::Input);
//         // Insert the input statement.
//         self.inputs.insert(input);
//
//         Ok(())
//     }
//
//     // TODO (howardwu): Instructions should have annotations, and we should check them here.
//     /// Adds the given instruction to the function.
//     /// This method is called before a function is run.
//     ///
//     /// # Errors
//     /// This method will halt if there are no input statements in memory.
//     /// This method will halt if the maximum number of instructions has been reached.
//     /// This method will halt if any registers are already assigned.
//     /// This method will halt if the destination register already exists in memory.
//     /// This method will halt if the destination register locator does not monotonically increase.
//     /// This method will halt if any operand register does not already exist in memory.
//     /// This method will halt if any registers are already set.
//     #[inline]
//     pub fn add_instruction(&mut self, instruction: Instruction<N>) -> Result<()> {
//         // Ensure there are input statements in memory.
//         ensure!(!self.inputs.is_empty(), "Cannot add instructions before inputs have been added");
//
//         // Ensure the maximum number of instructions has not been exceeded.
//         ensure!(
//             self.instructions.len() <= N::MAX_INSTRUCTIONS,
//             "Cannot add more than {} instructions",
//             N::MAX_INSTRUCTIONS
//         );
//
//         // // Iterate over the operand registers.
//         // for register in instruction.operands().iter().filter_map(|operand| operand.register()) {
//         //     // Ensure the operand registers are defined.
//         //     if !self.registers.is_defined(register) {
//         //         P::halt(format!("Operand register {register} does not exist"))
//         //     }
//         //
//         //     // Ensure the operand registers are not already assigned.
//         //     if self.registers.is_assigned(register) {
//         //         P::halt(format!("Register {register} is already assigned"))
//         //     }
//         // }
//
//         // Insert the destination register.
//         self.registers.insert(instruction.destination(), RegisterType::Destination);
//         // Insert the instruction.
//         self.instructions.push(instruction);
//
//         Ok(())
//     }
//
//     /// Adds the output statement into memory.
//     /// This method is called before a function is run.
//     /// If the given output is for a definition, then the definition must be added before this method is called.
//     ///
//     /// # Errors
//     /// This method will halt if there are no input statements or instructions in memory.
//     /// This method will halt if the maximum number of outputs has been reached.
//     /// This method will halt if the given output register is new.
//     /// This method will halt if the given output register is already set.
//     /// This method will halt if the given output annotation references a non-existent definition.
//     #[inline]
//     pub fn add_output(&mut self, output: Output<N>) -> Result<()> {
//         // Ensure there are input statements and instructions in memory.
//         ensure!(!self.inputs.is_empty(), "Cannot add outputs before inputs have been added");
//         ensure!(!self.instructions.is_empty(), "Cannot add outputs before instructions have been added");
//
//         // Ensure the maximum number of outputs has not been exceeded.
//         ensure!(self.outputs.len() <= N::MAX_OUTPUTS, "Cannot add more than {} outputs", N::MAX_OUTPUTS);
//
//         // Retrieve the output register.
//         let register = output.register();
//         // Ensure the output exists in the registers.
//         ensure!(self.registers.contains_key(&register), "Output register {register} does not exist");
//
//         // // If the output annotation is for a definition, ensure the output is referencing a valid definition.
//         // if let Annotation::Definition(identifier) = output.annotation() {
//         //     if !P::contains_definition(identifier) {
//         //         P::halt("Output annotation references non-existent definition")
//         //     }
//         // }
//
//         // If the output register is an input register, inform the user to allow them to ensure this is intended behavior.
//         if let Some(RegisterType::Input) = self.registers.get(&register) {
//             // warn!("Output register {register} is an input register, and this is a passthrough value");
//             eprintln!("Output register {register} is an input register, and this is a passthrough value");
//         }
//
//         // Insert the output statement.
//         self.outputs.insert(output);
//
//         Ok(())
//     }
//
//     /// Evaluates the function on the given inputs.
//     ///
//     /// # Errors
//     /// This method will halt if there are no input statements or instructions in memory.
//     /// This method will halt if any registers are already assigned.
//     /// This method will halt if the given inputs are not the same length as the input statements.
//     #[inline]
//     pub fn evaluate(&self, inputs: &[Value<N>]) -> Vec<Value<N>> {
//         // Ensure there are input statements and instructions in memory.
//         if self.inputs.is_empty() || self.instructions.is_empty() {
//             P::halt("Cannot evaluate a function without input statements or instructions")
//         }
//
//         // Ensure the function is not already evaluated.
//         if self.registers.is_dirty() {
//             P::halt("Registers cannot contain assignments prior to evaluation")
//         }
//
//         // Ensure the number of inputs matches the number of input statements.
//         if self.inputs.len() != inputs.len() {
//             P::halt(format!("Expected {} inputs, but given {}", self.inputs.len(), inputs.len()))
//         }
//
//         // Assign the inputs and ensure they matches the input statements.
//         self.assign_inputs(inputs);
//
//         // Evaluate the instructions.
//         for instruction in self.instructions.iter() {
//             instruction.evaluate(&self.registers);
//         }
//
//         // Load the outputs.
//         let mut outputs = Vec::with_capacity(self.outputs.len());
//         for output in self.outputs.iter() {
//             // Load the value from the output register.
//             let register = output.register();
//             let value = self.registers.load(register);
//
//             // TODO (howardwu): When handling the TODO below, relax this to exclude checking the mode.
//             // Ensure the output plaintext type matches the annotation.
//             if &value.annotation() != output.annotation() {
//                 P::halt(format!("Output \'{register}\' has an incorrect annotation of {}", value.annotation()))
//             }
//
//             // TODO (howardwu): When handling the TODO below, relax this to exclude checking the mode.
//             // If the output annotation is a definition, ensure the output value matches the definition.
//             if let Annotation::Definition(definition_name) = output.annotation() {
//                 // Retrieve the definition from the program.
//                 match P::get_definition(definition_name) {
//                     // Ensure the value matches its expected definition.
//                     Some(definition) => {
//                         if !definition.matches(&value) {
//                             P::halt(format!("Output \'{register}\' does not match \'{definition_name}\'"))
//                         }
//                     }
//                     None => P::halt("Output \'{register}\' references a non-existent definition"),
//                 }
//             }
//
//             // TODO (howardwu): Add encryption against the caller's address for all private literals,
//             //  and inject the ciphertext as Mode::Public, along with a constraint enforcing equality.
//             //  For constant outputs, add an assert_eq on the register value - if it's constant,
//             //  the constraint will automatically be discarded, and if it's not, the constraint will
//             //  ensure the output register's value matches the newly-assigned hardcoded constant.
//             // // If the value contains any public literals, assign a new public variable for the public literal,
//             // // and add a constraint to enforce equality of the value.
//             // match &value {
//             //     Value::Literal(literal) => {
//             //         if literal.is_public() {
//             //             let public_literal = Literal::new(Mode::Public, literal.eject_value());
//             //             P::Environment::assert_eq(literal, public_literal);
//             //         }
//             //     }
//             //     Value::Definition(_, members) => {
//             //         for member in members.iter() {
//             //             if member.is_public() {
//             //                 let public_literal = Literal::new(Mode::Public, member.eject_value());
//             //                 P::Environment::assert_eq(member, public_literal);
//             //             }
//             //         }
//             //     }
//             // }
//
//             // Insert the value into the outputs.
//             outputs.push(value);
//         }
//
//         // Clear the register assignments.
//         self.registers.clear_assignments();
//
//         outputs
//     }
// }
//
// impl<N: Network> Function<N> {
//     /// Assigns the given input values to the corresponding registers in memory.
//     /// This method is called before a function is run.
//     ///
//     /// # Errors
//     /// This method will halt if the input register was previously stored.
//     /// This method will halt if the input statement does not exist.
//     /// This method will halt if the annotation does not match.
//     #[inline]
//     fn assign_inputs(&self, values: &[Value<N>]) {
//         // Zip the input statements and input values together.
//         for (input, value) in self.inputs.iter().zip_eq(values.iter()) {
//             // Ensure the input value annotation matches the expected input annotation.
//             let register = input.register();
//             if &value.annotation() != input.annotation() {
//                 P::halt(format!("Input \'{register}\' has an incorrect annotation of {}", value.annotation()))
//             }
//
//             // If the input annotation is a definition, ensure the input value matches the definition.
//             if let Annotation::Definition(definition_name) = input.annotation() {
//                 // Retrieve the definition from the program.
//                 match P::get_definition(definition_name) {
//                     // Ensure the value matches its expected definition.
//                     Some(definition) => {
//                         if !definition.matches(value) {
//                             P::halt(format!("Input \'{register}\' does not match \'{definition_name}\'"))
//                         }
//                     }
//                     None => P::halt("Input \'{register}\' references a non-existent definition"),
//                 }
//             }
//
//             // Assign the input value to the register.
//             // This call will halt if the register is a register member, or if the register is already assigned.
//             self.registers.assign(register, value.clone());
//
//             // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
//         }
//     }
// }
//
// impl<N: Network> Parser for Function<N> {
//     /// Parses a string into a function.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self> {
//         // Parse the whitespace and comments from the string.
//         let (string, _) = Sanitizer::parse(string)?;
//         // Parse the 'function' keyword from the string.
//         let (string, _) = tag(Self::type_name())(string)?;
//         // Parse the space from the string.
//         let (string, _) = tag(" ")(string)?;
//         // Parse the function name from the string.
//         let (string, name) = Identifier::<N>::parse(string)?;
//         // Parse the colon ':' keyword from the string.
//         let (string, _) = tag(":")(string)?;
//
//         // Parse the inputs from the string.
//         let (string, inputs) = many1(Input::parse)(string)?;
//         // Parse the instructions from the string.
//         let (string, instructions) = many1(Instruction::parse)(string)?;
//         // Parse the outputs from the string.
//         let (string, outputs) = many0(Output::parse)(string)?;
//
//         // Initialize a new function.
//         let function = Self::new(name.as_str());
//         inputs.into_iter().for_each(|input| function.add_input(input));
//         instructions.into_iter().for_each(|instruction| function.add_instruction(instruction));
//         outputs.into_iter().for_each(|output| function.add_output(output));
//
//         Ok((string, function))
//     }
// }
//
// impl<N: Network> TypeName for Function<N> {
//     /// Returns the type name as a string.
//     #[inline]
//     fn type_name() -> &'static str {
//         "function"
//     }
// }
//
// #[allow(clippy::format_push_string)]
// impl<N: Network> fmt::Display for Function<N> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         // Write the function to a string.
//         let mut function = format!("{} {}:\n", Self::type_name(), self.name);
//         self.inputs.iter().for_each(|input| function.push_str(&format!("    {}\n", input)));
//         self.instructions.iter().for_each(|instruction| function.push_str(&format!("    {}\n", instruction)));
//         self.outputs.iter().for_each(|output| function.push_str(&format!("    {}\n", output)));
//         function.pop(); // trailing newline
//
//         write!(f, "{}", function)
//     }
// }
//
// impl<N: Network> FromBytes for Function<N> {
//     #[inline]
//     fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
//         // Read the function name.
//         let name = Identifier::<N>::read_le(&mut reader)?;
//
//         // Read the inputs.
//         let num_inputs = u16::read_le(&mut reader)?;
//         let mut inputs = Vec::with_capacity(num_inputs as usize);
//         for _ in 0..num_inputs {
//             inputs.push(Input::read_le(&mut reader)?);
//         }
//
//         // Read the instructions.
//         let num_instructions = u32::read_le(&mut reader)?;
//         let mut instructions = Vec::with_capacity(num_instructions as usize);
//         for _ in 0..num_instructions {
//             instructions.push(Instruction::read_le(&mut reader)?);
//         }
//
//         // Read the outputs.
//         let num_outputs = u16::read_le(&mut reader)?;
//         let mut outputs = Vec::with_capacity(num_outputs as usize);
//         for _ in 0..num_outputs {
//             outputs.push(Output::read_le(&mut reader)?);
//         }
//
//         // Initialize a new function.
//         let function = Self::new(name.as_str());
//         inputs.into_iter().for_each(|input| function.add_input(input));
//         instructions.into_iter().for_each(|instruction| function.add_instruction(instruction));
//         outputs.into_iter().for_each(|output| function.add_output(output));
//
//         Ok(function)
//     }
// }
//
// impl<N: Network> ToBytes for Function<N> {
//     #[inline]
//     fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
//         // Write the function name.
//         self.name.write_le(&mut writer)?;
//
//         // Write the number of inputs for the function.
//         let num_inputs = self.inputs.len();
//         match num_inputs <= P::NUM_INPUTS {
//             true => (num_inputs as u16).write_le(&mut writer)?,
//             false => return Err(error(format!("Failed to write {num_inputs} inputs as bytes"))),
//         }
//
//         // Write the inputs.
//         for input in self.inputs.iter() {
//             input.write_le(&mut writer)?;
//         }
//
//         // Write the number of instructions for the function.
//         let num_instructions = self.instructions.len();
//         match num_instructions <= P::NUM_INPUTS {
//             true => (num_instructions as u32).write_le(&mut writer)?,
//             false => return Err(error(format!("Failed to write {num_instructions} instructions as bytes"))),
//         }
//
//         // Write the instructions.
//         for instruction in self.instructions.iter() {
//             instruction.write_le(&mut writer)?;
//         }
//
//         // Write the number of outputs for the function.
//         let num_outputs = self.outputs.len();
//         match num_outputs <= P::NUM_INPUTS {
//             true => (num_outputs as u16).write_le(&mut writer)?,
//             false => return Err(error(format!("Failed to write {num_outputs} outputs as bytes"))),
//         }
//
//         // Write the outputs.
//         for output in self.outputs.iter() {
//             output.write_le(&mut writer)?;
//         }
//
//         Ok(())
//     }
// }
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use snarkvm_console_network::Testnet3;
//
//     type CurrentNetwork = Testnet3;
//
//     #[test]
//     fn test_function_evaluate() {
//         let function = Function::<CurrentNetwork>::from_str(
//             r"
// function foo:
//     input r0 as field.public;
//     input r1 as field.private;
//     add r0 r1 into r2;
//     output r2 as field.private;",
//         );
//         let first = Value::<CurrentNetwork>::from_str("2field.public");
//         let second = Value::from_str("3field.private");
//
//         // Run the function.
//         let expected = Value::<CurrentNetwork>::from_str("5field.private");
//         let candidate = function.evaluate(&[first.clone(), second.clone()]);
//         assert_eq!(expected.to_string(), candidate[0].to_string());
//
//         // Re-run to ensure state continues to work.
//         let expected = Value::<CurrentNetwork>::from_str("5field.private");
//         let candidate = function.evaluate(&[first, second]);
//         assert_eq!(expected.to_string(), candidate[0].to_string());
//     }
//
//     #[test]
//     fn test_function_parse() {
//         let function = Function::<CurrentNetwork>::parse(
//             r"
// function foo:
//     input r0 as field.public;
//     input r1 as field.private;
//     add r0 r1 into r2;
//     output r2 as field.private;
// ",
//         )
//         .unwrap()
//         .1;
//         assert_eq!("foo", function.name().to_string());
//         assert_eq!(2, function.inputs.len());
//         assert_eq!(1, function.instructions.len());
//         assert_eq!(1, function.outputs.len());
//     }
//
//     #[test]
//     fn test_function_display() {
//         let expected = r"function foo:
//     input r0 as field.public;
//     input r1 as field.private;
//     add r0 r1 into r2;
//     output r2 as field.private;";
//         let function = Function::<CurrentNetwork>::parse(expected).unwrap().1;
//         assert_eq!(expected, format!("{function}"),);
//     }
//
//     #[test]
//     fn test_function_bytes() {
//         let function_string = r"
// function main:
//     input r0 as field.public;
//     input r1 as field.private;
//     add r0 r1 into r2;
//     add r0 r1 into r3;
//     add r0 r1 into r4;
//     add r0 r1 into r5;
//     add r0 r1 into r6;
//     add r0 r1 into r7;
//     add r0 r1 into r8;
//     add r0 r1 into r9;
//     add r0 r1 into r10;
//     add r0 r1 into r11;
//     output r11 as field.private;";
//
//         let expected = Function::<CurrentNetwork>::from_str(function_string);
//         let expected_bytes = expected.to_bytes_le().unwrap();
//         println!("String size: {:?}, Bytecode size: {:?}", function_string.as_bytes().len(), expected_bytes.len());
//
//         let candidate = Function::<CurrentNetwork>::from_bytes_le(&expected_bytes).unwrap();
//         assert_eq!(expected.to_string(), candidate.to_string());
//         assert_eq!(expected_bytes, candidate.to_bytes_le().unwrap());
//     }
// }
