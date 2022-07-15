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
    pub fn run<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>)> {
        // Retrieve the main program.
        let program = self.program();
        // Retrieve the program ID.
        let program_id = program.id();
        // Ensure that the function exists.
        if !program.contains_function(&function_name) {
            bail!("Function '{function_name}' does not exist.")
        }

        // Construct the process.
        let process = self.get_process::<A>()?;

        // Authorize the function call.
        let authorization = process.authorize(private_key, program_id, function_name, inputs, rng)?;

        // Prepare the locator.
        let locator = Locator::<N>::from_str(&format!("{}/{}", program_id, function_name))?;
        println!("🚀 Executing '{}'...\n", locator.to_string().bold());

        // Prepare the build directory.
        let build_directory = self.build_directory();
        // Load the prover.
        let prover = ProverFile::open(&build_directory, &function_name)?;
        // Load the verifier.
        let verifier = VerifierFile::open(&build_directory, &function_name)?;

        // Adds the circuit key to the process.
        process.insert_circuit_key(
            program_id,
            &function_name,
            prover.proving_key().clone(),
            verifier.verifying_key().clone(),
        );

        // Execute the circuit.
        let (response, execution) = process.execute(authorization, &mut rand::thread_rng())?;

        Ok((response, execution))
    }
}
