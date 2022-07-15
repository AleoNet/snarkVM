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
    pub fn is_build_required<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(&self) -> Result<bool> {
        // Retrieve the main program.
        let program = self.program();

        // Prepare the build directory.
        let build_directory = self.build_directory();
        // If the build directory does not exist, then the package is stale.
        if !build_directory.exists() {
            return Ok(true);
        }

        // Initialize a boolean indicator if we need to build the circuit.
        let mut requires_build = true;
        // If the main AVM file exists, check if the AVM and Aleo file matches, to determine if we can skip.
        if AVMFile::<N>::main_exists_at(&build_directory) {
            // Retrieve the main AVM file.
            let candidate = AVMFile::open(&build_directory, &self.program_id, true)?;
            // Check if the program bytes matches.
            if candidate.program().to_bytes_le()? == program.to_bytes_le()? {
                // Next, check if the prover and verifier exist for each function.
                for function_name in program.functions().keys() {
                    // Check if the prover file exists.
                    if !ProverFile::exists_at(&build_directory, function_name) {
                        // If not, we need to build the circuit.
                        break;
                    }
                    // Check if the verifier file exists.
                    if !VerifierFile::exists_at(&build_directory, function_name) {
                        // If not, we need to build the circuit.
                        break;
                    }
                }
                // The program bytes matches, and all provers and verifiers exist, so we can skip the build.
                requires_build = false;
            }
        }

        Ok(requires_build)
    }
}
