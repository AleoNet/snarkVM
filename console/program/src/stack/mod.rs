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

mod instruction;
pub(crate) use instruction::*;

mod load;
mod store;

use crate::{
    program::RegisterTypes,
    Entry,
    Identifier,
    Literal,
    Plaintext,
    Program,
    Record,
    Register,
    Value,
    ValueType,
};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
pub enum StackValue<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A record value.
    Record(Record<N, Plaintext<N>>),
}

#[derive(Clone)]
pub struct Stack<N: Network> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned input registers to their values.
    input_registers: IndexMap<u64, Value<N, Plaintext<N>>>,
    /// The mapping of assigned destination registers to their values.
    destination_registers: IndexMap<u64, StackValue<N>>,
}

impl<N: Network> Stack<N> {
    /// Returns the program.
    #[inline]
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate(
        program: Program<N>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Retrieve the function from the program.
        let function = program.get_function(function_name)?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the register types.
        let register_types = program.get_function_registers(function_name)?;

        // Initialize the stack.
        let mut stack =
            Self { program, register_types, input_registers: IndexMap::new(), destination_registers: IndexMap::new() };

        // Initialize the input registers.
        for ((input_register, value_type), input) in stack.register_types.to_inputs().zip_eq(inputs.iter()) {
            // Ensure the input value matches the declared type in the register.
            stack.program.matches_input(input, &value_type)?;

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.

            // Assign the input value to the register.
            stack.input_registers.insert(input_register.locator(), match (input.clone(), value_type) {
                (StackValue::Plaintext(plaintext), ValueType::Constant(..)) => Value::Constant(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Public(..)) => Value::Public(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Private(..)) => Value::Private(plaintext),
                (StackValue::Record(record), ValueType::Record(..)) => Value::Record(record),
                _ => bail!("Input value does not match the input register type."),
            });
        }

        // Evaluate the function.
        {
            // Ensure there are input statements and instructions in memory.
            ensure!(!function.inputs().is_empty(), "Cannot evaluate a function without input statements");
            ensure!(!function.instructions().is_empty(), "Cannot evaluate a function without instructions");

            // Evaluate the instructions.
            function.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut stack))?;
        }

        // Initialize a vector to store the outputs.
        let mut outputs = Vec::with_capacity(function.outputs().len());

        // Load the outputs.
        for (register, value_type) in stack.register_types.to_outputs() {
            // Retrieve the stack value from the register.
            let register_value = stack.load(&Operand::Register(register.clone()))?;

            // Convert the stack value to the output value type.
            let output_value = match (register_value, value_type) {
                (StackValue::Plaintext(plaintext), ValueType::Constant(..)) => Value::Constant(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Public(..)) => Value::Public(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Private(..)) => Value::Private(plaintext),
                (StackValue::Record(record), ValueType::Record(..)) => Value::Record(record),
                _ => bail!("Stack value does not match the expected output type"),
            };

            // Ensure the output value matches the value type.
            stack.program.matches_value(&output_value, &value_type)?;
            // Insert the value into the outputs.
            outputs.push(output_value);

            // TODO (howardwu): Add encryption against the caller's address for all private literals,
            //  and inject the ciphertext as Mode::Public, along with a constraint enforcing equality.
            //  For constant outputs, add an assert_eq on the stack value - if it's constant,
            //  the constraint will automatically be discarded, and if it's not, the constraint will
            //  ensure the output register's value matches the newly-assigned hardcoded constant.
            // // If the value contains any public literals, assign a new public variable for the public literal,
            // // and add a constraint to enforce equality of the value.
            // match &value {
            //     Value::Literal(literal) => {
            //         if literal.is_public() {
            //             let public_literal = Literal::new(Mode::Public, literal.eject_value());
            //             P::Environment::assert_eq(literal, public_literal);
            //         }
            //     }
            //     Value::Definition(_, members) => {
            //         for member in members.iter() {
            //             if member.is_public() {
            //                 let public_literal = Literal::new(Mode::Public, member.eject_value());
            //                 P::Environment::assert_eq(member, public_literal);
            //             }
            //         }
            //     }
            // }
        }

        Ok(outputs)
    }
}
