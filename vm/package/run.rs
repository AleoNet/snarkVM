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
    /// Runs a program function with the given inputs.
    pub fn run<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
        request: &Request<N>,
    ) -> Result<(Response<N>, Execution<N>)> {
        // Ensure the network ID matches.
        ensure!(
            **request.network_id() == N::ID,
            "Network ID mismatch. Expected {}, but found {}",
            N::ID,
            request.network_id()
        );

        // Retrieve the main program.
        let program = self.program_file.program();
        // Retrieve the program ID.
        let program_id = program.id();
        // Ensure the program ID matches.
        if program_id != request.program_id() {
            bail!("The program '{}' does not exist. Expected {}.", request.program_id(), program_id);
        }
        // Ensure that the function exists.
        if !self.program_file().program().contains_function(request.function_name()) {
            bail!("Function '{}' does not exist.", request.function_name())
        }

        // Prepare the build directory.
        let mut build_directory = self.directory.clone();
        build_directory.push("build");

        // Create the build directory.
        if !build_directory.exists() {
            std::fs::create_dir_all(&build_directory)?;
        }

        // Create the process.
        let process = Process::<N, A>::new(program.clone())?;

        // Load the prover.
        let prover = ProverFile::open(&build_directory, request.function_name())?;
        // Load the verifier.
        let verifier = VerifierFile::open(&build_directory, request.function_name())?;

        // Execute the circuit.
        let (response, execution) = process.execute_synthesized(
            request,
            prover.proving_key(),
            verifier.verifying_key(),
            &mut rand::thread_rng(),
        )?;

        Ok((response, execution))
    }
}
