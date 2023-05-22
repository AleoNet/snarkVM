// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use snarkvm_synthesizer::CallMetrics;

impl<N: Network> Package<N> {
    /// Runs a program function with the given inputs.
    #[allow(clippy::type_complexity)]
    pub fn run<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>, R: Rng + CryptoRng>(
        &self,
        endpoint: Option<String>,
        private_key: &PrivateKey<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>, Inclusion<N>, Vec<CallMetrics<N>>)> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();
        // Ensure that the function exists.
        if !program.contains_function(&function_name) {
            bail!("Function '{function_name}' does not exist.")
        }

        // Build the package, if the package requires building.
        self.build::<A>(endpoint)?;

        // Prepare the locator (even if logging is disabled, to sanity check the locator is well-formed).
        let _locator = Locator::<N>::from_str(&format!("{program_id}/{function_name}"))?;

        #[cfg(feature = "aleo-cli")]
        println!("🚀 Executing '{}'...\n", _locator.to_string().bold());

        // Construct the process.
        let process = self.get_process()?;
        // Authorize the function call.
        let authorization = process.authorize::<A, R>(private_key, program_id, function_name, inputs.iter(), rng)?;

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
        let (response, execution, inclusion, metrics) = process.execute::<A, R>(authorization, rng)?;

        Ok((response, execution, inclusion, metrics))
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_utilities::TestRng;

    type CurrentAleo = snarkvm_circuit::network::AleoV0;

    #[test]
    fn test_run() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package();

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();
        // Ensure the build directory exists.
        assert!(package.build_directory().exists());

        // Initialize an RNG.
        let rng = &mut TestRng::default();
        // Sample the function inputs.
        let (private_key, function_name, inputs) =
            crate::package::test_helpers::sample_package_run(package.program_id());
        // Run the program function.
        let (_response, _execution, _inclusion, _metrics) =
            package.run::<CurrentAleo, _>(None, &private_key, function_name, &inputs, rng).unwrap();

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_run_with_import() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package_with_import();

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();
        // Ensure the build directory exists.
        assert!(package.build_directory().exists());

        // Initialize an RNG.
        let rng = &mut TestRng::default();
        // Sample the function inputs.
        let (private_key, function_name, inputs) =
            crate::package::test_helpers::sample_package_run(package.program_id());
        // Run the program function.
        let (_response, _execution, _inclusion, _metrics) =
            package.run::<CurrentAleo, _>(None, &private_key, function_name, &inputs, rng).unwrap();

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }
}
