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
mod matches;
mod sample;
mod store;

use crate::{CircuitKeys, Closure, Function, Instruction, Operand, Program, ProvingKey, Transition, VerifyingKey};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{
        Balance,
        Entry,
        EntryType,
        Identifier,
        Interface,
        Literal,
        LiteralType,
        Locator,
        Owner,
        Plaintext,
        PlaintextType,
        ProgramID,
        Record,
        RecordType,
        Register,
        RegisterType,
        Request,
        Response,
        Value,
        ValueType,
        U64,
    },
};

use indexmap::IndexMap;
use parking_lot::RwLock;
use std::{collections::VecDeque, sync::Arc};

#[derive(Clone)]
pub struct Authorization<N: Network>(Arc<RwLock<VecDeque<Request<N>>>>);

impl<N: Network> Authorization<N> {
    /// Initialize a new `Authorization` instance, with the given requests.
    pub fn new(requests: &[Request<N>]) -> Self {
        Self(Arc::new(RwLock::new(VecDeque::from_iter(requests.iter().cloned()))))
    }

    /// Returns the next `Request` in the authorization.
    pub fn peek_next(&self) -> Result<Request<N>> {
        self.get(0)
    }

    /// Returns the next `Request` from the authorization.
    pub fn next(&self) -> Result<Request<N>> {
        self.0.write().pop_front().ok_or_else(|| anyhow!("No more requests in the authorization"))
    }

    /// Returns the `Request` at the given index.
    pub fn get(&self, index: usize) -> Result<Request<N>> {
        self.0.read().get(index).cloned().ok_or_else(|| anyhow!("Attempted to 'get' missing request {index}"))
    }

    /// Returns the number of `Request`s in the authorization.
    pub fn len(&self) -> usize {
        self.0.read().len()
    }

    /// Return `true` if the authorization is empty.
    pub fn is_empty(&self) -> bool {
        self.0.read().is_empty()
    }

    /// Appends the given `Request` to the authorization.
    pub fn push(&self, request: Request<N>) {
        self.0.write().push_back(request);
    }

    /// Returns the requests in the authorization.
    pub fn to_vec_deque(&self) -> VecDeque<Request<N>> {
        self.0.read().clone()
    }
}

#[derive(Clone)]
pub struct Execution<N: Network>(Arc<RwLock<Vec<Transition<N>>>>);

impl<N: Network> Execution<N> {
    /// Initialize a new `Execution` instance.
    pub fn new() -> Self {
        Self(Arc::new(RwLock::new(Vec::new())))
    }

    /// Initializes a new `Execution` instance with the given transitions.
    pub fn from(transitions: &[Transition<N>]) -> Self {
        Self(Arc::new(RwLock::new(transitions.to_vec())))
    }

    /// Returns the `Transition` at the given index.
    pub fn get(&self, index: usize) -> Result<Transition<N>> {
        self.0.read().get(index).cloned().ok_or_else(|| anyhow!("Attempted to 'get' missing transition {index}"))
    }

    /// Returns the number of `Transition`s in the execution.
    pub fn len(&self) -> usize {
        self.0.read().len()
    }

    /// Return `true` if the execution is empty.
    pub fn is_empty(&self) -> bool {
        self.0.read().is_empty()
    }

    /// Returns the next `Transition` in the execution.
    pub fn peek(&self) -> Result<Transition<N>> {
        self.get(self.len() - 1)
    }

    /// Appends the given `Transition` to the execution.
    pub fn push(&self, transition: Transition<N>) {
        self.0.write().push(transition);
    }

    /// Pops the last `Transition` from the execution.
    pub fn pop(&self) -> Result<Transition<N>> {
        self.0.write().pop().ok_or_else(|| anyhow!("No more transitions in the execution"))
    }

    /// Returns the transitions in the execution.
    pub fn to_vec(&self) -> Vec<Transition<N>> {
        self.0.read().clone()
    }
}

impl<N: Network> Default for Execution<N> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone)]
pub enum CallStack<N: Network> {
    Authorize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    Synthesize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    Execute(Authorization<N>, Execution<N>),
}

impl<N: Network> CallStack<N> {
    /// Pushes the request to the stack.
    pub fn push(&mut self, request: Request<N>) -> Result<()> {
        match self {
            CallStack::Authorize(requests, ..) => requests.push(request),
            CallStack::Synthesize(requests, ..) => requests.push(request),
            CallStack::Execute(authorization, ..) => authorization.push(request),
        }
        Ok(())
    }

    /// Pops the request from the stack.
    pub fn pop(&mut self) -> Result<Request<N>> {
        match self {
            CallStack::Authorize(requests, ..) | CallStack::Synthesize(requests, ..) => {
                requests.pop().ok_or_else(|| anyhow!("No more requests on the stack"))
            }
            CallStack::Execute(authorization, ..) => authorization.next(),
        }
    }
}

#[derive(Clone)]
pub struct Stack<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: CircuitKeys<N>,
    /// The mapping of external stacks as `(program ID, stack)`.
    external_stacks: IndexMap<ProgramID<N>, Stack<N, A>>,
    /// The mapping of closure and function names to their register types.
    program_types: IndexMap<Identifier<N>, RegisterTypes<N>>,
    /// The current call stack.
    call_stack: CallStack<N>,
    /// The current circuit caller.
    circuit_caller: Option<circuit::Address<A>>,
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
    pub fn new(program: Program<N>, circuit_keys: CircuitKeys<N>) -> Result<Self> {
        // TODO (howardwu): Process every closure and function before returning.
        Ok(Self {
            program,
            circuit_keys,
            external_stacks: IndexMap::new(),
            program_types: IndexMap::new(),
            call_stack: CallStack::Execute(Authorization::new(&[]), Execution::new()),
            circuit_caller: None,
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
    pub fn get_external_record(&self, locator: &Locator<N>) -> Result<RecordType<N>> {
        // Retrieve the external program.
        let external_program = self.get_external_program(locator.program_id())?;
        // Return the external record, if it exists.
        external_program.get_record(locator.resource())
    }

    /// Returns the proving key for the given function name.
    #[inline]
    pub fn get_proving_key(&self, function_name: &Identifier<N>) -> Result<ProvingKey<N>> {
        // Return the proving key, if it exists.
        self.circuit_keys.get_proving_key(self.program_id(), function_name)
    }

    /// Returns the verifying key for the given function name.
    #[inline]
    pub fn get_verifying_key(&self, function_name: &Identifier<N>) -> Result<VerifyingKey<N>> {
        // Return the verifying key, if it exists.
        self.circuit_keys.get_verifying_key(self.program_id(), function_name)
    }

    /// Synthesizes the proving key and verifying key for the given function name.
    #[inline]
    pub fn synthesize_key<R: Rng + CryptoRng>(&self, function_name: &Identifier<N>, rng: &mut R) -> Result<()> {
        // Retrieve the program ID.
        let program_id = self.program.id();
        // Retrieve the function input types.
        let input_types = self.program.get_function(function_name)?.input_types();

        // Initialize a burner private key.
        let burner_private_key = PrivateKey::new(rng)?;
        // Compute the burner address.
        let burner_address = Address::try_from(&burner_private_key)?;
        // Sample the inputs.
        let inputs = input_types
            .iter()
            .map(|input_type| match input_type {
                ValueType::ExternalRecord(locator) => {
                    // Retrieve the external stack.
                    let stack = self.get_external_stack(locator.program_id())?;
                    // Sample the input.
                    stack.sample_value(&burner_address, &ValueType::Record(*locator.resource()), rng)
                }
                _ => self.sample_value(&burner_address, input_type, rng),
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute the request, with a burner private key.
        let request = Request::sign(&burner_private_key, *program_id, *function_name, &inputs, &input_types, rng)?;
        // Ensure the request is well-formed.
        ensure!(request.verify(), "Request is invalid");
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        // Initialize the call stack.
        let call_stack = CallStack::Synthesize(vec![request], burner_private_key, authorization);
        // Clone the stack.
        let mut stack = self.clone();
        // Synthesize the circuit.
        let _response = stack.execute_function(call_stack, rng)?;
        Ok(())
    }

    /// Returns the call stack.
    #[inline]
    pub fn call_stack(&self) -> CallStack<N> {
        self.call_stack.clone()
    }

    /// Returns the circuit caller.
    #[inline]
    pub fn circuit_caller(&self) -> Result<&circuit::Address<A>> {
        self.circuit_caller.as_ref().ok_or_else(|| anyhow!("Malformed stack: missing circuit caller"))
    }

    /// Returns the register types for the given closure or function name.
    #[inline]
    pub fn get_register_types(&self, name: &Identifier<N>) -> Result<&RegisterTypes<N>> {
        // Retrieve the register types.
        self.program_types.get(name).ok_or_else(|| anyhow!("Register types for '{name}' does not exist"))
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
        self.circuit_caller = None;
        self.register_types = self.get_register_types(closure.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            self.store(register, input.clone())
        })?;

        // Evaluate the instructions.
        for instruction in closure.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            self.load(&Operand::Register(output.register().clone()))
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
        self.circuit_caller = None;
        self.register_types = self.get_register_types(function.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            self.store(register, input.clone())
        })?;

        // Evaluate the instructions.
        for instruction in function.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
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
        call_stack: CallStack<N>,
    ) -> Result<Vec<circuit::Value<A>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Initialize the stack.
        self.call_stack = call_stack;
        self.circuit_caller = None;
        self.register_types = self.get_register_types(closure.name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // If the circuit is in execute mode, then store the console input.
            if let CallStack::Execute(..) = self.call_stack {
                use circuit::Eject;
                // Assign the console input to the register.
                self.store(register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            self.store_circuit(register, input.clone())
        })?;

        // Execute the instructions.
        for instruction in closure.instructions() {
            // If the circuit is in execute mode, then evaluate the instructions.
            if let CallStack::Execute(..) = self.call_stack {
                // If the evaluation fails, bail and return the error.
                if let Err(error) = instruction.evaluate(self) {
                    bail!("Failed to evaluate instruction ({instruction}): {error}");
                }
            }
            // Execute the instruction.
            instruction.execute(self)?;
        }

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Illegal closure operation: instructions injected public variables");

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
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
    pub fn execute_function<R: Rng + CryptoRng>(
        &mut self,
        call_stack: CallStack<N>,
        rng: &mut R,
    ) -> Result<Response<N>> {
        // Ensure the circuit environment is clean.
        A::reset();

        // Initialize the stack.
        self.call_stack = call_stack;
        let console_request = self.call_stack.pop()?;
        self.circuit_caller = None;
        self.register_types = self.get_register_types(console_request.function_name())?.clone();
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Ensure the network ID matches.
        ensure!(
            **console_request.network_id() == N::ID,
            "Network ID mismatch. Expected {}, but found {}",
            N::ID,
            console_request.network_id()
        );

        // Retrieve the program ID.
        let program_id = *console_request.program_id();
        // Retrieve the function from the program.
        let function = self.program.get_function(console_request.function_name())?;
        // Retrieve the number of inputs.
        let num_inputs = function.inputs().len();
        // Ensure the number of inputs matches the number of input statements.
        if num_inputs != console_request.inputs().len() {
            bail!("Expected {num_inputs} inputs, found {}", console_request.inputs().len())
        }

        use circuit::{Eject, Inject};

        // Inject the transition public key `tpk` as `Mode::Public`.
        let tpk = circuit::Group::<A>::new(circuit::Mode::Public, console_request.to_tpk());
        // Inject the request as `Mode::Private`.
        let request = circuit::Request::new(circuit::Mode::Private, console_request.clone());
        // Ensure the request has a valid signature, inputs, and transition view key.
        A::assert(request.verify(&tpk));
        // Cache the request caller.
        self.circuit_caller = Some(request.caller().clone());

        #[cfg(debug_assertions)]
        Self::log_circuit("Request");

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(request.inputs()).try_for_each(|(register, input)| {
            // If the circuit is in execute mode, then store the console input.
            if let CallStack::Execute(..) = self.call_stack {
                // Assign the console input to the register.
                self.store(register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            self.store_circuit(register, input.clone())
        })?;

        // Initialize a tracker to determine if there are any function calls.
        let mut contains_function_call = false;

        // Execute the instructions.
        for instruction in function.instructions() {
            // If the circuit is in execute mode, then evaluate the instructions.
            if let CallStack::Execute(..) = self.call_stack {
                // If the evaluation fails, bail and return the error.
                if let Err(error) = instruction.evaluate(self) {
                    bail!("Failed to evaluate instruction ({instruction}): {error}");
                }
            }

            // Execute the instruction.
            instruction.execute(self)?;

            // If the instruction was a function call, then set the tracker to `true`.
            if let Instruction::Call(call) = instruction {
                // Check if the call is a function call.
                if call.is_function_call(self)? {
                    contains_function_call = true;
                }
            }
        }

        // Load the outputs.
        let outputs = function
            .outputs()
            .iter()
            .map(|output| self.load_circuit(&Operand::Register(output.register().clone())))
            .collect::<Result<Vec<_>>>()?;

        #[cfg(debug_assertions)]
        Self::log_circuit(format!("Function '{}()'", function.name()));

        // If the function does not contain function calls, ensure no new public variables were injected.
        if !contains_function_call {
            // Ensure the number of public variables remains the same.
            ensure!(A::num_public() == num_public, "Instructions in function injected public variables");
        }

        // Construct the response.
        let response = circuit::Response::from_outputs(
            request.program_id(),
            num_inputs,
            request.tvk(),
            outputs,
            &function.output_types(),
        );

        #[cfg(debug_assertions)]
        Self::log_circuit("Response");

        use circuit::{ToField, Zero};

        let mut i64_balance = circuit::I64::zero();
        let mut field_balance = circuit::Field::zero();

        // Increment the balance by the amount in each record input.
        for input in request.inputs() {
            match input {
                // Dereference the record balance to retrieve the u64 balance.
                circuit::Value::Record(record) => {
                    // Retrieve the record balance.
                    let record_balance = &**record.balance();
                    // Increment the i64 balance.
                    i64_balance += record_balance.clone().cast_as_dual();
                    // Increment the field balance.
                    field_balance += record_balance.to_field();
                }
                // Skip iterations that are not records.
                _ => continue,
            }
        }

        // Ensure the i64 balance matches the field balance.
        A::assert_eq(i64_balance.to_field(), &field_balance);

        // Decrement the balance by the amount in each record output.
        for output in response.outputs() {
            match output {
                // Dereference the balance to retrieve the u64 balance.
                circuit::Value::Record(record) => {
                    // Retrieve the record balance.
                    let record_balance = &**record.balance();
                    // Decrement the i64 balance.
                    i64_balance -= record_balance.clone().cast_as_dual();
                    // Decrement the field balance.
                    field_balance -= record_balance.to_field();
                }
                // Skip iterations that are not records.
                _ => continue,
            }
        }

        // If the program and function is not a coinbase function, then ensure the i64 balance is positive.
        if !Self::is_coinbase(&program_id, function.name()) {
            use circuit::MSB;

            // Ensure the i64 balance MSB is false.
            A::assert(!i64_balance.msb());
            // Ensure the i64 balance matches the field balance.
            A::assert_eq(i64_balance.to_field(), &field_balance);

            // Inject the field balance as `Mode::Public`.
            let public_balance = circuit::Field::<A>::new(circuit::Mode::Public, field_balance.eject_value());
            // Ensure the injected field balance matches.
            A::assert_eq(public_balance, field_balance);

            #[cfg(debug_assertions)]
            println!("Logging fee: {}", i64_balance.eject_value());
        } else {
            // Inject the field balance as `Mode::Public`.
            let public_balance = circuit::Field::<A>::new(circuit::Mode::Public, i64_balance.to_field().eject_value());
            // Ensure the injected i64 balance matches.
            A::assert_eq(public_balance, &i64_balance);
        }

        #[cfg(debug_assertions)]
        Self::log_circuit("Complete");

        // Eject the fee.
        let fee = i64_balance.eject_value();
        // Eject the response.
        let response = response.eject_value();

        // If the circuit is in execute mode, then ensure the circuit is satisfied.
        if let CallStack::Execute(..) = self.call_stack {
            // If the circuit is not satisfied, then throw an error.
            ensure!(A::is_satisfied(), "'{program_id}/{}' is not satisfied on the given inputs.", function.name());
        }

        // Eject the circuit assignment and reset the circuit.
        let assignment = A::eject_assignment_and_reset();

        // If the circuit is **not** in authorize mode, synthesize the circuit key if it does not exist.
        if !matches!(self.call_stack, CallStack::Authorize(..)) {
            // If the circuit key does not exist, then synthesize it.
            if !self.circuit_keys.contains_key(&program_id, function.name()) {
                // Add the circuit key to the mapping.
                self.circuit_keys.insert_from_assignment(&program_id, function.name(), &assignment)?;
            }
        }

        // If the circuit is in execute mode, then execute the circuit into a transition.
        if let CallStack::Execute(_, ref execution) = self.call_stack {
            // #[cfg(debug_assertions)]
            for ((console_index, console_register), (circuit_index, circuit_register)) in
                self.console_registers.iter().zip_eq(&self.circuit_registers)
            {
                // Ensure the console and circuit index match (executed in same order).
                if *console_index != *circuit_index {
                    bail!("Console and circuit register indices are mismatching ({console_index} != {circuit_index})")
                }
                // Ensure the console and circuit registers match (executed to same value).
                if console_register != &circuit_register.eject_value() {
                    bail!("The console and circuit register values do not match at index {console_index}")
                }
            }

            // Retrieve the proving key.
            let proving_key = self.circuit_keys.get_proving_key(&program_id, function.name())?;
            // Execute the circuit.
            let proof = proving_key.prove(function.name(), &assignment, rng)?;
            // Add the transition to the execution.
            execution.push(Transition::from(&console_request, &response, proof, *fee)?);
        }

        // Return the response.
        Ok(response)
    }

    /// Returns `true` if the given program ID and function name corresponds to a coinbase function.
    #[inline]
    pub fn is_coinbase(program_id: &ProgramID<N>, function_name: &Identifier<N>) -> bool {
        program_id.to_string() == "stake.aleo" && function_name.to_string() == "initialize"
    }

    /// Prints the current state of the circuit.
    fn log_circuit<S: Into<String>>(scope: S) {
        use colored::Colorize;

        // Determine if the circuit is satisfied.
        let is_satisfied = if A::is_satisfied() { "✅".green() } else { "❌".red() };
        // Determine the count.
        let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();

        // Print the log.
        println!(
            "{is_satisfied} {:width$} (Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})",
            scope.into().bold(),
            width = 20
        );
    }
}
