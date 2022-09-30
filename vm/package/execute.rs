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

use snarkvm_compiler::Transaction;
use snarkvm_console::{
    program::{Plaintext, Record},
    types::Address,
};

use super::*;

pub struct ExecutionRequest<N: Network> {
    transaction: Transaction<N>,
    address: Address<N>,
    program_id: ProgramID<N>,
}

impl<N: Network> ExecutionRequest<N> {
    /// Sends the request to the given endpoint.
    pub fn new(transaction: Transaction<N>, address: Address<N>, program_id: ProgramID<N>) -> Self {
        Self { transaction, address, program_id }
    }

    /// Sends the request to the given endpoint.
    pub fn send(&self, endpoint: &str) -> Result<ExecuteResponse<N>> {
        Ok(ureq::post(endpoint).send_json(self)?.into_json()?)
    }

    /// Returns the deployment transaction.
    pub const fn transaction(&self) -> &Transaction<N> {
        &self.transaction
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
        let mut request = serializer.serialize_struct("ExecuteRequest", 3)?;
        // Serialize the deployment.
        request.serialize_field("transaction", &self.transaction)?;
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
            // Retrieve the execution transaction.
            serde_json::from_value(request["transaction"].clone()).map_err(de::Error::custom)?,
            // Retrieve the address of the program.
            serde_json::from_value(request["address"].clone()).map_err(de::Error::custom)?,
            // Retrieve the program ID.
            serde_json::from_value(request["program_id"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

pub struct ExecuteResponse<N: Network> {
    transaction: Transaction<N>,
}

impl<N: Network> ExecuteResponse<N> {
    /// Initializes a new deploy response.
    pub const fn new(transaction: Transaction<N>) -> Self {
        Self { transaction }
    }

    /// Returns the execution transaction.
    pub const fn transaction(&self) -> &Transaction<N> {
        &self.transaction
    }
}

impl<N: Network> Serialize for ExecuteResponse<N> {
    /// Serializes the deploy response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("ExecuteResponse", 1)?;
        response.serialize_field("transaction", &self.transaction)?;
        response.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for ExecuteResponse<N> {
    /// Deserializes the deploy response from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the response from a string into a value.
        let response = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the execution transaction.
            serde_json::from_value(response["transaction"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

impl<N: Network> Package<N> {
    pub fn execute<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>, R: Rng + CryptoRng>(
        &self,
        endpoint: Option<String>,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<(Response<N>, Transaction<N>)> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();
        // Ensure that the function exists.
        if !program.contains_function(&function_name) {
            bail!("Function '{function_name}' does not exist.")
        }

        // Build the package, if the package requires building.
        // TODO: Remove this None and do things the reasonable way
        self.build::<A>(None)?;

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
        let (execution_response, execution) = process.execute::<A, R>(authorization, rng)?;

        // Execute the additional fee.
        let (_, additional_fee) = process.execute_additional_fee::<A, _>(private_key, credits, 1, rng)?;

        // TODO: the additional_fee should not be optional.
        let execution_transaction = Transaction::from_execution(execution, Some(additional_fee))?;

        let caller = self.manifest_file().development_address();

        match endpoint {
            Some(ref endpoint) => {
                // Construct the deploy request.
                let request = ExecutionRequest::new(execution_transaction, *caller, *program_id);
                // Send the deploy request.
                let response = request.send(endpoint)?;
                Ok((execution_response, response.transaction))
            }
            None => Ok((execution_response, execution_transaction)),
        }
    }
}

// TODO: Fix tests
// #[cfg(test)]
// mod tests {
//     use super::*;

//     type CurrentNetwork = snarkvm_console::network::Testnet3;
//     type CurrentAleo = snarkvm_circuit::network::AleoV0;

//     #[test]
//     fn test_execute() {
//         // Samples a new package at a temporary directory.
//         let (directory, package) = crate::package::test_helpers::sample_package();

//         // Deploy the package.
//         let (execution_response, execution_transaction) = package.execute::<CurrentAleo>(None).unwrap();
//         if let Transaction::Execute(_, execution, _) = execution_transaction {
//             // Ensure the deployment edition matches.
//             assert_eq!(<CurrentNetwork as Network>::EDITION, execution.edition());
//             // TODO: check the transitions
//             // TODO: check the execution response.
//         }

//         // Proactively remove the temporary directory (to conserve space).
//         std::fs::remove_dir_all(directory).unwrap();
//     }

//     #[test]
//     fn test_execute_with_import() {
//         // Samples a new package at a temporary directory.
//         let (directory, package) = crate::package::test_helpers::sample_package_with_import();

//         // Deploy the package.
//         let (execution_response, execution_transaction) = package.execute::<CurrentAleo>(None).unwrap();
//         if let Transaction::Execute(_, execution, _) = execution_transaction {
//             // Ensure the deployment edition matches.
//             assert_eq!(<CurrentNetwork as Network>::EDITION, execution.edition());
//             // TODO: check the transitions
//             // TODO: check the execution response.
//         }

//         // Proactively remove the temporary directory (to conserve space).
//         std::fs::remove_dir_all(directory).unwrap();
//     }
// }
