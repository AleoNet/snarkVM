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

impl<N: Network> Package<N> {
    /// Builds the package.
    pub fn build<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(&self) -> Result<()> {
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

        // Load each function circuit.
        for function_name in program.functions().keys() {
            // Synthesize the proving and verifying key.
            process.synthesize_key::<A, _>(program_id, function_name, &mut rand::thread_rng())?;

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
