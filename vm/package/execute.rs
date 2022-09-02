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

use snarkvm_compiler::Execution;
use snarkvm_console::types::Address;

use super::*;

pub struct ExecutionRequest<N: Network> {
    execution: Execution<N>,
    address: Address<N>,
    program_id: ProgramID<N>,
}

impl<N: Network> ExecutionRequest<N> {
    /// Returns a new execution request.
    pub fn new(execution: Execution<N>, address: Address<N>, program_id: ProgramID<N>) -> Self {
        Self { execution, address, program_id }
    }

    /// Sends the request to the given endpoint.
    pub fn send(&self, endpoint: &str) -> Result<ExecutionResponse<N>> {
        Ok(ureq::post(endpoint).send_json(self)?.into_json()?)
    }

    /// Returns the execution.
    pub const fn execution(&self) -> &Execution<N> {
        &self.execution
    }

    /// Returns the program address.
    pub const fn address(&self) -> &Address<N> {
        &self.address
    }

    /// Returns the imports.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }
}

impl<N: Network> Serialize for ExecutionRequest<N> {
    /// Serializes the deploy request into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut request = serializer.serialize_struct("ExecutionRequest", 3)?;
        // Serialize the execution.
        request.serialize_field("execution", &self.execution)?;
        // Serialize the address.
        request.serialize_field("address", &self.address)?;
        // Serialize the program id.
        request.serialize_field("program_id", &self.program_id)?;
        request.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for ExecutionRequest<N> {
    /// Deserializes the deploy request from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the request from a string into a value.
        let request = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the execution.
            serde_json::from_value(request["execution"].clone()).map_err(de::Error::custom)?,
            // Retrieve the address of the user executing.
            serde_json::from_value(request["address"].clone()).map_err(de::Error::custom)?,
            // Retrieve the program ID.
            serde_json::from_value(request["program_id"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

pub struct ExecutionResponse<N: Network> {
    execution: Execution<N>,
}

impl<N: Network> ExecutionResponse<N> {
    /// Initializes a new execution response.
    pub const fn new(execution: Execution<N>) -> Self {
        Self { execution }
    }

    /// Returns the execution.
    pub const fn execution(&self) -> &Execution<N> {
        &self.execution
    }
}

impl<N: Network> Serialize for ExecutionResponse<N> {
    /// Serializes the execution response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("ExecutionResponse", 1)?;
        response.serialize_field("execution", &self.execution)?;
        response.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for ExecutionResponse<N> {
    /// Deserializes the execution response from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the response from a string into a value.
        let response = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the execution.
            serde_json::from_value(response["execution"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

impl<N: Network> Package<N> {
    pub fn execute<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>, R: Rng + CryptoRng>(
        &self,
        endpoint: Option<String>,
        private_key: &PrivateKey<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Execution<N>> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();
        // Ensure that the function exists.
        if !program.contains_function(&function_name) {
            bail!("Function '{function_name}' does not exist.")
        }

        // Build the package, if the package requires building.
        // TODO: Remove this clone and do things the reasonable way
        // TODO: Executing before building will fail. We need to handle the build request in snarkOS's server.
        self.build::<A>(endpoint.clone())?;

        // Prepare the locator (even if logging is disabled, to sanity check the locator is well-formed).
        let _locator = Locator::<N>::from_str(&format!("{program_id}/{function_name}"))?;

        #[cfg(feature = "aleo-cli")]
        println!("🚀 Executing '{}'...\n", _locator.to_string().bold());

        // Construct the process.
        let process = self.get_process()?;
        // Authorize the function call.
        let authorization = process.authorize::<A, R>(private_key, program_id, function_name, inputs, rng)?;

        // Retrieve the program.
        let program = process.get_program(program_id)?;
        // Retrieve the function from the program.
        let function = program.get_function(&function_name)?;
        // Save all the prover and verifier files for any function calls that are made.
        for instruction in function.instructions() {
            if let Instruction::Call(call) = instruction {
                // Retrieve the program and resource.
                let (program, resource) = match call.operator() {
                    CallOperator::Locator(locator) => (process.get_program(locator.program_id())?, locator.resource()),
                    CallOperator::Resource(resource) => (program, resource),
                };
                // If this is a function call, save its corresponding prover and verifier files.
                if program.contains_function(resource) {
                    // Set the function name to the resource, in this scope.
                    let function_name = resource;
                    // Prepare the build directory for the imported program.
                    let import_build_directory =
                        self.build_directory().join(format!("{}-{}", program.id().name(), program.id().network()));

                    // Create the prover.
                    let prover = ProverFile::open(&import_build_directory, function_name)?;
                    // Adds the proving key to the process.
                    process.insert_proving_key(program.id(), function_name, prover.proving_key().clone())?;

                    // Create the verifier.
                    let verifier = VerifierFile::open(&import_build_directory, function_name)?;
                    // Adds the verifying key to the process.
                    process.insert_verifying_key(program.id(), function_name, verifier.verifying_key().clone())?;
                }
            }
        }

        // Prepare the build directory.
        let build_directory = self.build_directory();
        // Load the prover.
        let prover = ProverFile::open(&build_directory, &function_name)?;
        // Load the verifier.
        let verifier = VerifierFile::open(&build_directory, &function_name)?;

        // Adds the proving key to the process.
        process.insert_proving_key(program_id, &function_name, prover.proving_key().clone())?;
        // Adds the verifying key to the process.
        process.insert_verifying_key(program_id, &function_name, verifier.verifying_key().clone())?;

        // Execute the circuit.
        let (_response, execution) = process.execute::<A, R>(authorization, rng)?;

        let caller = self.manifest_file().development_address();

        match endpoint {
            Some(ref endpoint) => {
                // Construct the deploy request.
                let request = ExecutionRequest::new(execution, *caller, *program_id);
                // Send the deploy request.
                let response = request.send(endpoint)?;

                Ok(response.execution)
            }
            None => Ok(execution),
        }
    }
}
