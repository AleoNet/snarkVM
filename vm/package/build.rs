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

use super::*;

pub struct BuildRequest<N: Network> {
    program: Program<N>,
    imports: Vec<Program<N>>,
    function_name: Identifier<N>,
}

impl<N: Network> BuildRequest<N> {
    /// Initializes a new build request.
    pub const fn new(program: Program<N>, imports: Vec<Program<N>>, function_name: Identifier<N>) -> Self {
        Self { program, imports, function_name }
    }

    /// Sends the request to the given endpoint.
    pub fn send(&self, endpoint: &str) -> Result<BuildResponse<N>> {
        Ok(ureq::get(endpoint).send_json(self)?.into_json()?)
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns the imports.
    pub const fn imports(&self) -> &Vec<Program<N>> {
        &self.imports
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }
}

impl<N: Network> Serialize for BuildRequest<N> {
    /// Serializes the build request into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut request = serializer.serialize_struct("BuildRequest", 3)?;
        request.serialize_field("program", &self.program)?;
        request.serialize_field("imports", &self.imports)?;
        request.serialize_field("function_name", &self.function_name)?;
        request.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for BuildRequest<N> {
    /// Deserializes the build request from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the request from a string into a value.
        let request = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program.
            serde_json::from_value(request["program"].clone()).map_err(de::Error::custom)?,
            // Retrieve the imports.
            serde_json::from_value(request["imports"].clone()).map_err(de::Error::custom)?,
            // Retrieve the function name.
            serde_json::from_value(request["function_name"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

pub struct BuildResponse<N: Network> {
    program_id: ProgramID<N>,
    function_name: Identifier<N>,
    proving_key: ProvingKey<N>,
    verifying_key: VerifyingKey<N>,
}

impl<N: Network> BuildResponse<N> {
    /// Initializes a new build response.
    pub const fn new(
        program_id: ProgramID<N>,
        function_name: Identifier<N>,
        proving_key: ProvingKey<N>,
        verifying_key: VerifyingKey<N>,
    ) -> Self {
        Self { program_id, function_name, proving_key, verifying_key }
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }

    /// Returns the proving key.
    pub const fn proving_key(&self) -> &ProvingKey<N> {
        &self.proving_key
    }

    /// Returns the verifying key.
    pub const fn verifying_key(&self) -> &VerifyingKey<N> {
        &self.verifying_key
    }
}

impl<N: Network> Serialize for BuildResponse<N> {
    /// Serializes the build response into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut response = serializer.serialize_struct("BuildResponse", 4)?;
        response.serialize_field("program_id", &self.program_id)?;
        response.serialize_field("function_name", &self.function_name)?;
        response.serialize_field("proving_key", &self.proving_key)?;
        response.serialize_field("verifying_key", &self.verifying_key)?;
        response.end()
    }
}

impl<'de, N: Network> Deserialize<'de> for BuildResponse<N> {
    /// Deserializes the build response from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Parse the response from a string into a value.
        let response = serde_json::Value::deserialize(deserializer)?;
        // Recover the leaf.
        Ok(Self::new(
            // Retrieve the program ID.
            serde_json::from_value(response["program_id"].clone()).map_err(de::Error::custom)?,
            // Retrieve the function name.
            serde_json::from_value(response["function_name"].clone()).map_err(de::Error::custom)?,
            // Retrieve the proving key.
            serde_json::from_value(response["proving_key"].clone()).map_err(de::Error::custom)?,
            // Retrieve the verifying key.
            serde_json::from_value(response["verifying_key"].clone()).map_err(de::Error::custom)?,
        ))
    }
}

impl<N: Network> Package<N> {
    /// Builds the package.
    pub fn build<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
        endpoint: Option<String>,
    ) -> Result<()> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();

        // Prepare the build directory.
        let build_directory = self.build_directory();
        // Create the build directory if it does not exist.
        if !build_directory.exists() {
            std::fs::create_dir_all(&build_directory)?;
        }

        // Construct the process.
        let process = self.get_process()?;

        // Retrieve the imported programs.
        let imported_programs = program
            .imports()
            .keys()
            .map(|program_id| process.get_program(program_id).cloned())
            .collect::<Result<Vec<_>>>()?;

        // Synthesize each proving and verifying key.
        for function_name in program.functions().keys() {
            match endpoint {
                Some(ref endpoint) => {
                    // Prepare the request.
                    let request = BuildRequest::new(program.clone(), imported_programs.clone(), *function_name);
                    // Load the proving and verifying key.
                    let response = request.send(endpoint)?;
                    // Ensure the program ID matches.
                    ensure!(
                        response.program_id() == program_id,
                        "Program ID mismatch: {} != {program_id}",
                        response.program_id()
                    );
                    // Ensure the function name matches.
                    ensure!(
                        response.function_name() == function_name,
                        "Function name mismatch: {} != {function_name}",
                        response.function_name()
                    );
                    // Insert the proving key.
                    process.insert_proving_key(response.program_id(), function_name, response.proving_key().clone());
                    // Insert the verifying key.
                    process.insert_verifying_key(
                        response.program_id(),
                        function_name,
                        response.verifying_key().clone(),
                    );
                }
                None => process.synthesize_key::<A, _>(program_id, function_name, &mut rand::thread_rng())?,
            }
        }

        // Load each function circuit.
        for function_name in program.functions().keys() {
            // Retrieve the program.
            let program = process.get_program(program_id)?;
            // Retrieve the function from the program.
            let function = program.get_function(function_name)?;
            // Save all the prover and verifier files for any function calls that are made.
            for instruction in function.instructions() {
                if let Instruction::Call(call) = instruction {
                    // Retrieve the program and resource.
                    let (program, resource) = match call.operator() {
                        CallOperator::Locator(locator) => {
                            (process.get_program(locator.program_id())?, locator.resource())
                        }
                        CallOperator::Resource(resource) => (program, resource),
                    };
                    // If this is a function call, save its corresponding prover and verifier files.
                    if program.contains_function(resource) {
                        // Set the function name to the resource, in this scope.
                        let function_name = resource;
                        // Retrieve the proving key.
                        let proving_key = process.get_proving_key(program.id(), resource)?;
                        // Retrieve the verifying key.
                        let verifying_key = process.get_verifying_key(program.id(), resource)?;

                        // Prepare the build directory for the imported program.
                        let import_build_directory =
                            self.build_directory().join(format!("{}-{}", program.id().name(), program.id().network()));
                        // Create the build directory if it does not exist.
                        if !import_build_directory.exists() {
                            std::fs::create_dir_all(&import_build_directory)?;
                        }

                        // Create the prover.
                        let _prover = ProverFile::create(&import_build_directory, function_name, proving_key)?;
                        // Create the verifier.
                        let _verifier = VerifierFile::create(&import_build_directory, function_name, verifying_key)?;
                    }
                }
            }

            // Retrieve the proving key.
            let proving_key = process.get_proving_key(program_id, function_name)?;
            // Retrieve the verifying key.
            let verifying_key = process.get_verifying_key(program_id, function_name)?;

            // Create the prover.
            let _prover = ProverFile::create(&build_directory, function_name, proving_key)?;
            // Create the verifier.
            let _verifier = VerifierFile::create(&build_directory, function_name, verifying_key)?;
        }

        // Lastly, write the AVM file.
        let _avm_file = AVMFile::create(&build_directory, program.clone(), true)?;

        Ok(())
    }
}
