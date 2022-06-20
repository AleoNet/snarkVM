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

mod circuit_value;
pub(crate) use circuit_value::*;

mod stack_value;
pub use stack_value::*;

mod load;
mod store;

use crate::vm::{Operand, Program, RegisterTypes};
use console::{
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, Record, Register, RegisterType, Value, ValueType},
};

use indexmap::IndexMap;

pub struct Stack<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N, A>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned console registers to their values.
    console_registers: IndexMap<u64, StackValue<N>>,
    /// The mapping of assigned circuit registers to their values.
    circuit_registers: IndexMap<u64, CircuitValue<A>>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub fn new(program: Program<N, A>, register_types: RegisterTypes<N>) -> Result<Self> {
        // Ensure the input registers are locators.
        for (register, _) in register_types.to_input_types() {
            ensure!(matches!(register, Register::Locator(_)), "Expected locator, found {register}");
        }

        Ok(Self { program, register_types, console_registers: IndexMap::new(), circuit_registers: IndexMap::new() })
    }

    /// Returns the program.
    #[inline]
    pub const fn program(&self) -> &Program<N, A> {
        &self.program
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

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate(
        program: Program<N, A>,
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
        let mut stack = Self::new(program, register_types.clone())?;

        // Initialize the input registers.
        for (((register, register_type), input), value_type) in register_types
            .to_input_types()
            .zip_eq(inputs.iter())
            .zip_eq(function.inputs().iter().map(|i| i.value_type()))
        {
            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
            // Assign the input to the register.
            stack.store(&register, input.clone())?;
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

    /// Executes a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute(
        program: Program<N, A>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<circuit::Value<A, circuit::Plaintext<A>>>> {
        // Retrieve the function from the program.
        let function = program.get_function(function_name)?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the register types.
        let register_types = program.get_function_registers(function_name)?;

        // Initialize the stack.
        let mut stack = Self::new(program, register_types.clone())?;

        // Initialize the input registers.
        for (((register, register_type), input), value_type) in register_types
            .to_input_types()
            .zip_eq(inputs.iter())
            .zip_eq(function.inputs().iter().map(|i| i.value_type()))
        {
            // Assign the console input to the register.
            stack.store(&register, input.clone())?;

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
            // Assign the circuit input to the register.
            stack.store_circuit(&register, match value_type {
                ValueType::Constant(..) => circuit::Inject::new(circuit::Mode::Constant, input.clone()),
                ValueType::Public(..) => circuit::Inject::new(circuit::Mode::Public, input.clone()),
                ValueType::Private(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                ValueType::Record(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
            })?;
        }

        // Execute the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut stack))?;
        function.instructions().iter().try_for_each(|instruction| instruction.execute(&mut stack))?;

        // Initialize a vector to store the outputs.
        let mut outputs = Vec::with_capacity(function.outputs().len());
        // Load the outputs.
        for ((register, register_type), value_type) in
            stack.to_output_types().zip_eq(function.outputs().iter().map(|o| o.value_type()))
        {
            // Retrieve the stack value from the register.
            let output = stack.load_circuit(&Operand::Register(register.clone()))?;

            // Convert the stack value to the output value type.
            let output = match (output, value_type) {
                (CircuitValue::Plaintext(plaintext), ValueType::Constant(..)) => circuit::Value::Constant(plaintext),
                (CircuitValue::Plaintext(plaintext), ValueType::Public(..)) => circuit::Value::Public(plaintext),
                (CircuitValue::Plaintext(plaintext), ValueType::Private(..)) => circuit::Value::Private(plaintext),
                (CircuitValue::Record(record), ValueType::Record(..)) => circuit::Value::Record(record),
                _ => bail!("Stack value does not match the expected output type"),
            };

            // Ensure the output value matches the value type.
            stack.program.matches_value(&circuit::Eject::eject_value(&output), &value_type)?;
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
