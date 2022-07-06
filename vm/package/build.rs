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
        let program = self.program_file.program();
        // Retrieve the program ID.
        let program_id = program.id();

        // Prepare the build directory.
        let mut build_directory = self.directory.clone();
        build_directory.push("build");

        // Create the build directory.
        if !build_directory.exists() {
            std::fs::create_dir_all(&build_directory)?;
        }

        // If the main AVM file exists, check if its program checksum matches, to determine if we can skip.
        if AVMFile::<N>::main_exists_at(&build_directory) {
            // Retrieve the main AVM file.
            let candidate = AVMFile::open(&build_directory, &self.program_id, true)?;
            // Check if the program bytes matches.
            if candidate.program().to_bytes_le()? == program.to_bytes_le()? {
                // The program bytes matches, so we can skip the build.
                return Ok(());
            }
        }

        // Write the AVM file.
        let avm_file = AVMFile::create(&build_directory, program.clone(), true)?;

        // Create the process.
        let process = Process::<N, A>::new(program.clone())?;

        // Load each function circuit.
        for function_name in program.functions().keys() {
            // Synthesize the proving and verifying key.
            let (proving_key, verifying_key) = process.circuit_key(program_id, function_name)?;
        }

        Ok(())
    }
}
