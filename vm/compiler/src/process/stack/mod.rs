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

mod matches;
mod sample;

use crate::{
    Authorization,
    CallOperator,
    Certificate,
    CircuitKeys,
    Closure,
    Deployment,
    Execution,
    Function,
    Instruction,
    Operand,
    Program,
    ProvingKey,
    RegisterTypes,
    Registers,
    Transition,
    VerifyingKey,
};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{
        Balance,
        Entry,
        EntryType,
        Identifier,
        Literal,
        Locator,
        Owner,
        Plaintext,
        PlaintextType,
        ProgramID,
        Record,
        RecordType,
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
use std::sync::Arc;

pub type Assignments<N> = Arc<RwLock<Vec<circuit::Assignment<<N as Environment>::Field>>>>;

#[derive(Clone)]
pub enum CallStack<N: Network> {
    Authorize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    Synthesize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    CheckDeployment(Vec<Request<N>>, PrivateKey<N>, Assignments<N>),
    Evaluate,
    Execute(Authorization<N>, Arc<RwLock<Execution<N>>>),
}

impl<N: Network> CallStack<N> {
    /// Pushes the request to the stack.
    pub fn push(&mut self, request: Request<N>) -> Result<()> {
        match self {
            CallStack::Authorize(requests, ..) => requests.push(request),
            CallStack::Synthesize(requests, ..) => requests.push(request),
            CallStack::CheckDeployment(requests, ..) => requests.push(request),
            CallStack::Evaluate => (),
            CallStack::Execute(authorization, ..) => authorization.push(request),
        }
        Ok(())
    }

    /// Pops the request from the stack.
    pub fn pop(&mut self) -> Result<Request<N>> {
        match self {
            CallStack::Authorize(requests, ..)
            | CallStack::Synthesize(requests, ..)
            | CallStack::CheckDeployment(requests, ..) => {
                requests.pop().ok_or_else(|| anyhow!("No more requests on the stack"))
            }
            CallStack::Evaluate => bail!("No requests on the stack when in `evaluate` mode"),
            CallStack::Execute(authorization, ..) => authorization.next(),
        }
    }
}

#[derive(Clone)]
pub struct Stack<N: Network> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of external stacks as `(program ID, stack)`.
    external_stacks: IndexMap<ProgramID<N>, Stack<N>>,
    /// The mapping of closure and function names to their register types.
    program_types: IndexMap<Identifier<N>, RegisterTypes<N>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: CircuitKeys<N>,
}

impl<N: Network> Stack<N> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub fn new(program: Program<N>, circuit_keys: CircuitKeys<N>) -> Result<Self> {
        // TODO (howardwu): Process every closure and function before returning.
        Ok(Self { program, external_stacks: IndexMap::new(), program_types: IndexMap::new(), circuit_keys })
    }

    /// Adds a new external stack to the stack.
    #[inline]
    pub fn add_external_stack(&mut self, external_stack: Stack<N>) -> Result<()> {
        // Retrieve the program ID.
        let program_id = *external_stack.program_id();
        // Ensure the external stack is not already added.
        ensure!(!self.external_stacks.contains_key(&program_id), "Program '{program_id}' already exists");
        // Ensure the program exists in the main program imports.
        ensure!(self.program.contains_import(&program_id), "'{program_id}' does not exist in the main program imports");
        // Ensure the external stack is not for the main program.
        ensure!(self.program.id() != external_stack.program_id(), "External stack program cannot be the main program");
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
    pub fn get_external_stack(&self, program_id: &ProgramID<N>) -> Result<&Stack<N>> {
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

    /// Returns the function with the given function name.
    pub fn get_function(&self, function_name: &Identifier<N>) -> Result<Function<N>> {
        self.program.get_function(function_name)
    }

    /// Returns the expected number of calls for the given function name.
    #[inline]
    pub fn get_number_of_calls(&self, function_name: &Identifier<N>) -> Result<usize> {
        // Retrieve the function.
        let function = self.get_function(function_name)?;
        // Determine the number of calls for this function (including the function itself).
        let mut num_calls = 1;
        for instruction in function.instructions() {
            if let Instruction::Call(call) = instruction {
                // Determine if this is a function call.
                if call.is_function_call(self)? {
                    // Increment by the number of calls.
                    num_calls += match call.operator() {
                        CallOperator::Locator(locator) => {
                            self.get_external_stack(locator.program_id())?.get_number_of_calls(locator.resource())?
                        }
                        CallOperator::Resource(resource) => self.get_number_of_calls(resource)?,
                    };
                }
            }
        }
        Ok(num_calls)
    }

    /// Returns the register types for the given closure or function name.
    #[inline]
    pub fn get_register_types(&self, name: &Identifier<N>) -> Result<&RegisterTypes<N>> {
        // Retrieve the register types.
        self.program_types.get(name).ok_or_else(|| anyhow!("Register types for '{name}' does not exist"))
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
    pub fn synthesize_key<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        function_name: &Identifier<N>,
        rng: &mut R,
    ) -> Result<()> {
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
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        // Initialize the call stack.
        let call_stack = CallStack::Synthesize(vec![request], burner_private_key, authorization);
        // Synthesize the circuit.
        let _response = self.execute_function::<A, R>(call_stack, rng)?;
        Ok(())
    }

    /// Deploys the program with the given program ID, as a deployment.
    #[inline]
    pub fn deploy<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Deployment<N>> {
        // Ensure the program contains functions.
        ensure!(!self.program.functions().is_empty(), "Program '{}' has no functions", self.program.id());

        // Initialize a mapping for the bundle.
        let mut bundle = IndexMap::with_capacity(self.program.functions().len());

        for function_name in self.program.functions().keys() {
            // If the proving and verifying key do not exist, synthesize it.
            if !self.circuit_keys.contains_proving_key(self.program.id(), function_name)
                || !self.circuit_keys.contains_verifying_key(self.program.id(), function_name)
            {
                // Synthesize the proving and verifying key.
                self.synthesize_key::<A, R>(function_name, rng)?;
            }

            // Retrieve the proving key.
            let proving_key = self.get_proving_key(function_name)?;
            // Retrieve the verifying key.
            let verifying_key = self.get_verifying_key(function_name)?;

            // Certify the circuit.
            let certificate = Certificate::certify(function_name, &proving_key, &verifying_key)?;

            // Add the verifying key and certificate to the bundle.
            bundle.insert(*function_name, (verifying_key, certificate));
        }

        // Return the deployment.
        Ok(Deployment::new(N::EDITION, self.program.clone(), bundle))
    }

    /// Checks each function in the program on the given verifying key and certificate.
    #[inline]
    pub fn verify_deployment<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        verifying_keys: &IndexMap<Identifier<N>, (VerifyingKey<N>, Certificate<N>)>,
        rng: &mut R,
    ) -> Result<()> {
        // Retrieve the program.
        let program = &self.program;
        // Retrieve the program ID.
        let program_id = program.id();

        // Sanity Checks //

        // Ensure the program network-level domain (NLD) is correct.
        ensure!(program_id.is_aleo(), "Program '{program_id}' has an incorrect network-level domain (NLD)");
        // Ensure the program contains functions.
        ensure!(!program.functions().is_empty(), "No functions present in the deployment for program '{program_id}'");
        // Ensure the deployment contains verifying keys.
        ensure!(!verifying_keys.is_empty(), "No verifying keys present in the deployment for program '{program_id}'");

        // Check Verifying Keys //

        // Ensure the number of verifying keys matches the number of program functions.
        if verifying_keys.len() != program.functions().len() {
            bail!("The number of verifying keys does not match the number of program functions");
        }

        // Ensure the program functions are in the same order as the verifying keys.
        for ((function_name, function), candidate_name) in program.functions().iter().zip_eq(verifying_keys.keys()) {
            // Ensure the function name is correct.
            if function_name != function.name() {
                bail!("The function key is '{function_name}', but the function name is '{}'", function.name())
            }
            // Ensure the function name with the verifying key is correct.
            if candidate_name != function.name() {
                bail!("The verifier key is '{candidate_name}', but the function name is '{}'", function.name())
            }
        }

        // Iterate through the program functions.
        for (function, (verifying_key, certificate)) in program.functions().values().zip_eq(verifying_keys.values()) {
            // Initialize a burner private key.
            let burner_private_key = PrivateKey::new(rng)?;
            // Compute the burner address.
            let burner_address = Address::try_from(&burner_private_key)?;
            // Retrieve the input types.
            let input_types = function.input_types();
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
            let request =
                Request::sign(&burner_private_key, *program_id, *function.name(), &inputs, &input_types, rng)?;
            // Initialize the assignments.
            let assignments = Assignments::<N>::default();
            // Initialize the call stack.
            let call_stack = CallStack::CheckDeployment(vec![request], burner_private_key, assignments.clone());
            // Synthesize the circuit.
            let _response = self.execute_function::<A, R>(call_stack, rng)?;
            // Check the certificate.
            match assignments.read().last() {
                None => bail!("The assignment for function '{}' is missing in '{program_id}'", function.name()),
                Some(assignment) => {
                    // Ensure the certificate is valid.
                    if !certificate.verify(function.name(), assignment, verifying_key) {
                        bail!("The certificate for function '{}' is invalid in '{program_id}'", function.name())
                    }
                }
            };
        }

        Ok(())
    }

    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[Value<N>],
    ) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Initialize the registers.
        let mut registers =
            Registers::<N, A>::new(CallStack::Evaluate, self.get_register_types(closure.name())?.clone());

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;

        // Evaluate the instructions.
        for instruction in closure.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            registers.load(self, &Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_function<A: circuit::Aleo<Network = N>>(
        &self,
        function: &Function<N>,
        inputs: &[Value<N>],
    ) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches.
        if function.inputs().len() != inputs.len() {
            bail!(
                "Function '{}' in the program '{}' expects {} inputs, but {} were provided.",
                function.name(),
                self.program.id(),
                function.inputs().len(),
                inputs.len()
            )
        }

        // Initialize the registers.
        let mut registers =
            Registers::<N, A>::new(CallStack::Evaluate, self.get_register_types(function.name())?.clone());

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;

        // Evaluate the instructions.
        for instruction in function.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            registers.load(self, &Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Executes a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_closure<A: circuit::Aleo<Network = N>>(
        &self,
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

        // Initialize the registers.
        let mut registers = Registers::new(call_stack, self.get_register_types(closure.name())?.clone());

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // If the circuit is in execute mode, then store the console input.
            if let CallStack::Execute(..) = registers.call_stack() {
                use circuit::Eject;
                // Assign the console input to the register.
                registers.store(self, register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            registers.store_circuit(self, register, input.clone())
        })?;

        // Execute the instructions.
        for instruction in closure.instructions() {
            // If the circuit is in execute mode, then evaluate the instructions.
            if let CallStack::Execute(..) = registers.call_stack() {
                // If the evaluation fails, bail and return the error.
                if let Err(error) = instruction.evaluate(self, &mut registers) {
                    bail!("Failed to evaluate instruction ({instruction}): {error}");
                }
            }
            // Execute the instruction.
            instruction.execute(self, &mut registers)?;
        }

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Illegal closure operation: instructions injected public variables");

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            registers.load_circuit(self, &Operand::Register(output.register().clone()))
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
    pub fn execute_function<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        call_stack: CallStack<N>,
        rng: &mut R,
    ) -> Result<Response<N>> {
        // Ensure the circuit environment is clean.
        A::reset();

        // Clone the call stack.
        let mut call_stack = call_stack;
        // Retrieve the next request.
        let console_request = call_stack.pop()?;

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

        // Initialize the registers.
        let mut registers = Registers::new(call_stack, self.get_register_types(function.name())?.clone());

        // Ensure the inputs match their expected types.
        console_request.inputs().iter().zip_eq(&function.input_types()).try_for_each(|(input, input_type)| {
            // Ensure the input matches the input type in the substack function.
            self.matches_value_type(input, input_type)
        })?;

        // Ensure the request is well-formed.
        ensure!(console_request.verify(&function.input_types()), "Request is invalid");

        use circuit::{Eject, Inject};

        // Inject the transition public key `tpk` as `Mode::Public`.
        let tpk = circuit::Group::<A>::new(circuit::Mode::Public, console_request.to_tpk());
        // Inject the request as `Mode::Private`.
        let request = circuit::Request::new(circuit::Mode::Private, console_request.clone());
        // Ensure the request has a valid signature, inputs, and transition view key.
        A::assert(request.verify(&function.input_types(), &tpk));

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>("Request");

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(request.inputs()).try_for_each(|(register, input)| {
            // If the circuit is in execute mode, then store the console input.
            if let CallStack::Execute(..) = registers.call_stack() {
                // Assign the console input to the register.
                registers.store(self, register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            registers.store_circuit(self, register, input.clone())
        })?;

        // Initialize a tracker to determine if there are any function calls.
        let mut contains_function_call = false;

        // Execute the instructions.
        for instruction in function.instructions() {
            // If the circuit is in execute mode, then evaluate the instructions.
            if let CallStack::Execute(..) = registers.call_stack() {
                // If the evaluation fails, bail and return the error.
                if let Err(error) = instruction.evaluate(self, &mut registers) {
                    bail!("Failed to evaluate instruction ({instruction}): {error}");
                }
            }

            // Execute the instruction.
            instruction.execute(self, &mut registers)?;

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
            .map(|output| registers.load_circuit(self, &Operand::Register(output.register().clone())))
            .collect::<Result<Vec<_>>>()?;

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>(format!("Function '{}()'", function.name()));

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
        Self::log_circuit::<A, _>("Response");

        use circuit::{ToField, Zero};

        let mut i64_gates = circuit::I64::zero();
        let mut field_gates = circuit::Field::zero();

        // Increment the gates by the amount in each record input.
        for input in request.inputs() {
            match input {
                // Dereference the record gates to retrieve the u64 gates.
                circuit::Value::Record(record) => {
                    // Retrieve the record gates.
                    let record_gates = &**record.gates();
                    // Increment the i64 gates.
                    i64_gates += record_gates.clone().cast_as_dual();
                    // Increment the field gates.
                    field_gates += record_gates.to_field();
                }
                // Skip iterations that are not records.
                _ => continue,
            }
        }

        // Ensure the i64 gates matches the field gates.
        A::assert_eq(i64_gates.to_field(), &field_gates);

        // Decrement the gates by the amount in each record output.
        for output in response.outputs() {
            match output {
                // Dereference the gates to retrieve the u64 gates.
                circuit::Value::Record(record) => {
                    // Retrieve the record gates.
                    let record_gates = &**record.gates();
                    // Decrement the i64 gates.
                    i64_gates -= record_gates.clone().cast_as_dual();
                    // Decrement the field gates.
                    field_gates -= record_gates.to_field();
                }
                // Skip iterations that are not records.
                _ => continue,
            }
        }

        // If the program and function is not a coinbase function, then ensure the i64 gates is positive.
        if !Program::is_coinbase(&program_id, function.name()) {
            use circuit::MSB;

            // Ensure the i64 gates MSB is false.
            A::assert(!i64_gates.msb());
            // Ensure the i64 gates matches the field gates.
            A::assert_eq(i64_gates.to_field(), &field_gates);

            // Inject the field gates as `Mode::Public`.
            let public_gates = circuit::Field::<A>::new(circuit::Mode::Public, field_gates.eject_value());
            // Ensure the injected field gates matches.
            A::assert_eq(public_gates, field_gates);

            #[cfg(debug_assertions)]
            println!("Logging fee: {}", i64_gates.eject_value());
        } else {
            // Inject the field gates as `Mode::Public`.
            let public_gates = circuit::Field::<A>::new(circuit::Mode::Public, i64_gates.to_field().eject_value());
            // Ensure the injected i64 gates matches.
            A::assert_eq(public_gates, &i64_gates);
        }

        #[cfg(debug_assertions)]
        Self::log_circuit::<A, _>("Complete");

        // Eject the fee.
        let fee = i64_gates.eject_value();
        // Eject the response.
        let response = response.eject_value();

        // Ensure the outputs matches the expected value types.
        response.outputs().iter().zip_eq(&function.output_types()).try_for_each(|(output, output_type)| {
            // Ensure the output matches its expected type.
            self.matches_value_type(output, output_type)
        })?;

        // If the circuit is in `Execute` mode, then ensure the circuit is satisfied.
        if let CallStack::Execute(..) = registers.call_stack() {
            // If the circuit is not satisfied, then throw an error.
            ensure!(A::is_satisfied(), "'{program_id}/{}' is not satisfied on the given inputs.", function.name());
        }

        // Eject the circuit assignment and reset the circuit.
        let assignment = A::eject_assignment_and_reset();

        // If the circuit is in `Synthesize` or `Execute` mode, synthesize the circuit key, if it does not exist.
        if matches!(registers.call_stack(), CallStack::Synthesize(..))
            || matches!(registers.call_stack(), CallStack::Execute(..))
        {
            // If the proving key does not exist, then synthesize it.
            if !self.circuit_keys.contains_proving_key(&program_id, function.name()) {
                // Add the circuit key to the mapping.
                self.circuit_keys.insert_from_assignment(&program_id, function.name(), &assignment)?;
            }
        }

        // If the circuit is in `CheckDeployment` mode, then save the assignment.
        if let CallStack::CheckDeployment(_, _, ref assignments) = registers.call_stack() {
            // Add the assignment to the assignments.
            assignments.write().push(assignment);
        }
        // If the circuit is in `Execute` mode, then execute the circuit into a transition.
        else if let CallStack::Execute(_, ref execution) = registers.call_stack() {
            // #[cfg(debug_assertions)]
            registers.ensure_console_and_circuit_registers_match()?;

            // Retrieve the proving key.
            let proving_key = self.circuit_keys.get_proving_key(&program_id, function.name())?;
            // Execute the circuit.
            let proof = proving_key.prove(function.name(), &assignment, rng)?;
            // Construct the transition.
            let transition = Transition::from(&console_request, &response, &function.output_types(), proof, *fee)?;
            // Add the transition to the execution.
            execution.write().push(transition);
        }

        // Return the response.
        Ok(response)
    }

    /// Prints the current state of the circuit.
    fn log_circuit<A: circuit::Aleo<Network = N>, S: Into<String>>(scope: S) {
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

impl<N: Network> PartialEq for Stack<N> {
    fn eq(&self, other: &Self) -> bool {
        self.program == other.program
            && self.external_stacks == other.external_stacks
            && self.program_types == other.program_types
    }
}

impl<N: Network> Eq for Stack<N> {}
