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

mod register_types;
pub use register_types::*;

mod load;
mod store;

use crate::{Closure, Function, Operand, Program};
use console::{
    network::prelude::*,
    program::{
        Entry,
        EntryType,
        Identifier,
        Interface,
        Literal,
        LiteralType,
        Locator,
        Plaintext,
        PlaintextType,
        ProgramID,
        RecordType,
        Register,
        RegisterType,
        Request,
        Value,
        ValueType,
    },
};

use console::account::PrivateKey;
use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
pub struct StackCall<N: Network> {
    /// The list of children stack calls.
    subcalls: Vec<StackCall<N>>,
    /// The program ID.
    program_id: ProgramID<N>,
    /// The function name.
    function_name: Identifier<N>,
    /// The function inputs.
    inputs: Vec<Value<N>>,
    /// The function input types.
    input_types: Vec<ValueType<N>>,
}

impl<N: Network> StackCall<N> {
    /// Initializes a new stack call request.
    pub fn new(
        subcalls: &[StackCall<N>],
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        inputs: Vec<Value<N>>,
        input_types: Vec<ValueType<N>>,
    ) -> Self {
        Self {
            subcalls: subcalls.to_vec(),
            program_id: *program_id,
            function_name: *function_name,
            inputs,
            input_types,
        }
    }

    /// Returns the list of children stack calls.
    pub fn subcalls(&self) -> &[StackCall<N>] {
        &self.subcalls
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }

    /// Returns the function inputs.
    pub fn inputs(&self) -> &[Value<N>] {
        &self.inputs
    }

    /// Returns the function input types.
    pub fn input_types(&self) -> &[ValueType<N>] {
        &self.input_types
    }

    /// Authorizes an external call, with the given private key, input types, and RNG.
    pub fn authorize<R: Rng + CryptoRng>(&self, private_key: &PrivateKey<N>, rng: &mut R) -> Result<Request<N>> {
        Request::sign(private_key, self.program_id, self.function_name, &self.inputs, &self.input_types, rng)
    }

    /// Returns an iterator over the stack calls, including the current one (last).
    pub fn iter(&self) -> impl Iterator<Item = StackCall<N>> {
        vec![self.subcalls.clone(), vec![self.clone()]].into_iter().flatten()
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum StackMode {
    Authorize,
    Deploy,
    Execute,
}

#[derive(Clone)]
pub struct Stack<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of external stacks as `(program ID, stack)`.
    external_stacks: IndexMap<ProgramID<N>, Stack<N, A>>,
    /// The mapping of closure and function names to their register types.
    program_types: IndexMap<Identifier<N>, RegisterTypes<N>>,
    /// The current stack mode.
    stack_mode: StackMode,
    /// The list of external calls.
    external_calls: Vec<StackCall<N>>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned console registers to their values.
    console_registers: IndexMap<u64, Value<N>>,
    /// The mapping of assigned circuit registers to their values.
    circuit_registers: IndexMap<u64, circuit::Value<A>>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub fn new(program: Program<N>) -> Result<Self> {
        // TODO (howardwu): Process every closure and function before returning.
        Ok(Self {
            program,
            external_stacks: IndexMap::new(),
            program_types: IndexMap::new(),
            stack_mode: StackMode::Authorize,
            external_calls: Vec::new(),
            register_types: RegisterTypes::new(),
            console_registers: IndexMap::new(),
            circuit_registers: IndexMap::new(),
        })
    }

    /// Adds a new external stack to the stack.
    #[inline]
    pub fn add_external_stack(&mut self, external_stack: Stack<N, A>) -> Result<()> {
        // Retrieve the program ID.
        let program_id = *external_stack.program_id();
        // Ensure the external stack is not already added.
        ensure!(!self.external_stacks.contains_key(&program_id), "Program '{program_id}' already exists");
        // Ensure the program exists in the main program imports.
        ensure!(self.program.contains_import(&program_id), "'{program_id}' does not exist in the main program imports");
        // TODO (howardwu): Ensure the imported program is declared in the program imports.
        // TODO (howardwu): Ensure the imported program is not the main program.
        // Add the external stack to the stack.
        self.external_stacks.insert(program_id, external_stack);
        // Return success.
        Ok(())
    }

    /// Adds the given closure name and register types to the stack.
    #[inline]
    pub fn add_closure_types(&mut self, name: &Identifier<N>, register_types: RegisterTypes<N>) -> Result<()> {
        // Ensure the closure name is not already added.
        ensure!(!self.program_types.contains_key(name), "Closure '{name}' already exists");
        // Add the closure name and register types to the stack.
        self.program_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }

    /// Adds the given function name and register types to the stack.
    #[inline]
    pub fn add_function_types(&mut self, name: &Identifier<N>, register_types: RegisterTypes<N>) -> Result<()> {
        // Ensure the function name is not already added.
        ensure!(!self.program_types.contains_key(name), "Function '{name}' already exists");
        // Add the function name and register types to the stack.
        self.program_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }

    /// Returns the program.
    #[inline]
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns the program ID.
    #[inline]
    pub const fn program_id(&self) -> &ProgramID<N> {
        self.program.id()
    }

    /// Returns the stack mode.
    #[inline]
    pub const fn stack_mode(&self) -> StackMode {
        self.stack_mode
    }

    /// Returns the register types for the given closure or function name.
    #[inline]
    pub fn get_register_types(&self, name: &Identifier<N>) -> Result<&RegisterTypes<N>> {
        // Retrieve the register types.
        self.program_types.get(name).ok_or_else(|| anyhow!("Register types for '{name}' does not exist"))
    }

    /// Returns an iterator over the external calls.
    #[inline]
    pub fn external_calls(&self) -> &[StackCall<N>] {
        &self.external_calls
    }

    /// Returns an iterator over the (flattened) external calls.
    #[inline]
    pub fn external_calls_flattened(&self) -> impl '_ + Iterator<Item = StackCall<N>> {
        self.external_calls.iter().flat_map(|call| call.iter())
    }

    /// Adds the given as an external call to the stack.
    #[inline]
    pub fn add_external_call(&mut self, external_call: StackCall<N>) {
        self.external_calls.push(external_call);
    }

    /// Returns the external stack for the given program ID.
    #[inline]
    pub fn get_external_stack(&self, program_id: &ProgramID<N>) -> Result<&Stack<N, A>> {
        // Retrieve the external stack.
        self.external_stacks.get(program_id).ok_or_else(|| anyhow!("External program '{program_id}' does not exist."))
    }

    /// Returns the external program for the given program ID.
    #[inline]
    pub fn get_external_program(&self, program_id: &ProgramID<N>) -> Result<&Program<N>> {
        match self.program.id() == program_id {
            true => bail!("Attempted to get the main program '{}' as an external program", self.program.id()),
            // Retrieve the external stack, and return the external program.
            false => Ok(self.get_external_stack(program_id)?.program()),
        }
    }

    /// Returns `true` if the stack contains the external record.
    #[inline]
    pub fn contains_external_record(&self, locator: &Locator<N>) -> bool {
        // Retrieve the external program.
        match self.get_external_program(locator.program_id()) {
            // Return `true` if the external record exists.
            Ok(external_program) => external_program.contains_record(locator.resource()),
            // Return `false` otherwise.
            Err(_) => false,
        }
    }

    /// Returns `true` if the stack contains the external record.
    #[inline]
    pub fn get_external_record(&self, locator: &Locator<N>) -> Result<RecordType<N>> {
        // Retrieve the external program.
        let external_program = self.get_external_program(locator.program_id())?;
        // Return the external record, if it exists.
        external_program.get_record(locator.resource())
    }

    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_closure(&mut self, closure: &Closure<N>, inputs: &[Value<N>]) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Initialize the stack.
        self.register_types = self.get_register_types(closure.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            self.store(register, input.clone())
        })?;

        // Evaluate the instructions.
        closure.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            self.load(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Executes a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_closure(
        &mut self,
        closure: &Closure<N>,
        inputs: &[circuit::Value<A>],
        stack_mode: StackMode,
    ) -> Result<Vec<circuit::Value<A>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Initialize the stack.
        self.stack_mode = stack_mode;
        self.register_types = self.get_register_types(closure.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            use circuit::Eject;

            // If the circuit is in execute mode, then store the console input.
            if self.stack_mode == StackMode::Execute {
                // Assign the console input to the register.
                self.store(register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            self.store_circuit(register, input.clone())
        })?;

        // If the circuit is in execute mode, then evaluate the instructions.
        if self.stack_mode == StackMode::Execute {
            closure.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;
        }
        // Execute the instructions.
        closure.instructions().iter().try_for_each(|instruction| instruction.execute(self))?;

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Forbidden operation: instructions injected public variables");

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            self.load_circuit(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_function(&mut self, function: &Function<N>, inputs: &[Value<N>]) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Initialize the stack.
        self.register_types = self.get_register_types(function.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            self.store(register, input.clone())
        })?;

        // Evaluate the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            self.load(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Executes a program function on the given inputs.
    ///
    /// Note: To execute a transition, do **not** call this method. Instead, call `Process::execute`.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_function(
        &mut self,
        function: &Function<N>,
        inputs: &[circuit::Value<A>],
        stack_mode: StackMode,
    ) -> Result<Vec<circuit::Value<A>>> {
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Initialize the stack.
        self.stack_mode = stack_mode;
        self.register_types = self.get_register_types(function.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            use circuit::Eject;

            // If the circuit is in execute mode, then store the console input.
            if self.stack_mode == StackMode::Execute {
                // Assign the console input to the register.
                self.store(register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            self.store_circuit(register, input.clone())
        })?;

        // If the circuit is in execute mode, then evaluate the instructions.
        if self.stack_mode == StackMode::Execute {
            function.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;
        }
        // Execute the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.execute(self))?;

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Forbidden operation: instructions injected public variables");

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            self.load_circuit(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Executes a program function on the given inputs.
    ///
    /// Note: To execute a transition, do **not** call this method. Instead, call `Process::execute`.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_function_from_console(
        &mut self,
        function: &Function<N>,
        inputs: &[Value<N>],
        stack_mode: StackMode,
    ) -> Result<Vec<circuit::Value<A>>> {
        // Inject the inputs to the circuit environment.
        let inputs = function
            .inputs()
            .iter()
            .map(|i| i.value_type())
            .zip_eq(inputs)
            .map(|(value_type, input)| {
                // Inject the inputs based on their value type.
                match value_type {
                    ValueType::Constant(..) => circuit::Inject::new(circuit::Mode::Constant, input.clone()),
                    ValueType::Public(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                    ValueType::Private(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                    ValueType::Record(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                    ValueType::ExternalRecord(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                }
            })
            .collect::<Vec<_>>();
        // Execute the function.
        self.execute_function(&function, &inputs, stack_mode)
    }
}
