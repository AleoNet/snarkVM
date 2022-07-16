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
    /// Returns `true` if the package is stale or has not been built.
    pub fn is_build_required<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(&self) -> bool {
        // Prepare the build directory.
        let build_directory = self.build_directory();
        // If the build directory does not exist, then a build is required.
        if !build_directory.exists() {
            return true;
        }

        // If the main AVM file does not exists, then a build is required.
        if !AVMFile::<N>::main_exists_at(&build_directory) {
            return true;
        }

        // Open the main AVM file.
        let avm_file = match AVMFile::open(&build_directory, &self.program_id, true) {
            // Retrieve the main AVM file.
            Ok(file) => file,
            // If the main AVM file fails to open, then a build is required.
            Err(_) => return true,
        };

        // Initialize a boolean indicator if we need to build the circuit.
        let mut is_complete = true;

        // Check if the program ID in the manifest matches the program ID in the AVM file.
        if avm_file.program().id() == &self.program_id {
            // Retrieve the main program.
            let program = self.program();

            // Check if the program matches.
            if avm_file.program() == program {
                // Next, check if the prover and verifier exist for each function.
                for function_name in program.functions().keys() {
                    // Check if the prover file exists.
                    if !ProverFile::exists_at(&build_directory, function_name) {
                        // If not, we need to build the circuit.
                        is_complete = false;
                        break;
                    }
                    // Check if the verifier file exists.
                    if !VerifierFile::exists_at(&build_directory, function_name) {
                        // If not, we need to build the circuit.
                        is_complete = false;
                        break;
                    }
                }
            }
        }

        !is_complete
    }
}
