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
    RegisterType,
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
    input_registers: IndexMap<u64, StackValue<N>>,
    /// The mapping of assigned destination registers to their values.
    destination_registers: IndexMap<u64, StackValue<N>>,
}

impl<N: Network> Stack<N> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub(crate) fn new(program: Program<N>, register_types: RegisterTypes<N>) -> Result<Self> {
        // Ensure the input registers are locators.
        for (register, _) in register_types.to_input_types() {
            ensure!(matches!(register, Register::Locator(_)), "Expected locator, found {register}");
        }

        Ok(Self { program, register_types, input_registers: IndexMap::new(), destination_registers: IndexMap::new() })
    }

    /// Returns an iterator over all input register types.
    #[inline]
    pub fn to_input_types(&self) -> impl '_ + Iterator<Item = (Register<N>, RegisterType<N>)> {
        self.register_types.to_input_types()
    }

    /// Returns an iterator over all output register types.
    #[inline]
    pub fn to_output_types(&self) -> impl '_ + Iterator<Item = (&Register<N>, &RegisterType<N>)> {
        self.register_types.to_output_types()
    }

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
        // Ensure there are input statements in the function.
        ensure!(!function.inputs().is_empty(), "Cannot evaluate a function without input statements");
        // Ensure there are instructions in the function.
        ensure!(!function.instructions().is_empty(), "Cannot evaluate a function without instructions");

        // Retrieve the register types.
        let register_types = program.get_function_registers(function_name)?;

        // Initialize the stack.
        let mut stack = Self::new(program, register_types)?;

        // Initialize the input registers.
        for (((register, register_type), input), value_type) in stack
            .register_types
            .to_input_types()
            .zip_eq(inputs.iter())
            .zip_eq(function.inputs().iter().map(|i| i.value_type()))
        {
            // Ensure the input value matches the declared type in the register.
            stack.program.matches_input(input, &value_type)?;

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.

            // TODO (howardwu): In circuit, allocate using the value type.
            // stack.input_registers.insert(register.locator(), match (input.clone(), value_type) {
            //     (StackValue::Plaintext(plaintext), ValueType::Constant(..)) => Value::Constant(plaintext),
            //     (StackValue::Plaintext(plaintext), ValueType::Public(..)) => Value::Public(plaintext),
            //     (StackValue::Plaintext(plaintext), ValueType::Private(..)) => Value::Private(plaintext),
            //     (StackValue::Record(record), ValueType::Record(..)) => Value::Record(record),
            //     _ => bail!("Input value does not match the input register type."),
            // });

            // Assign the input to the register.
            stack.input_registers.insert(register.locator(), input.clone());
        }

        // Evaluate the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut stack))?;

        // Initialize a vector to store the outputs.
        let mut outputs = Vec::with_capacity(function.outputs().len());
        // Load the outputs.
        for ((register, register_type), value_type) in
            stack.to_output_types().zip_eq(function.outputs().iter().map(|o| o.value_type()))
        {
            // Retrieve the stack value from the register.
            let output = stack.load(&Operand::Register(register.clone()))?;

            // Convert the stack value to the output value type.
            let output = match (output, value_type) {
                (StackValue::Plaintext(plaintext), ValueType::Constant(..)) => Value::Constant(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Public(..)) => Value::Public(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Private(..)) => Value::Private(plaintext),
                (StackValue::Record(record), ValueType::Record(..)) => Value::Record(record),
                _ => bail!("Stack value does not match the expected output type"),
            };

            // Ensure the output value matches the value type.
            stack.program.matches_value(&output, &value_type)?;
            // Insert the value into the outputs.
            outputs.push(output);

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
