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

impl<N: Network> Process<N> {
    /// Deploys the program with the given program ID, as a deployment.
    #[inline]
    pub fn deploy<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        program_id: &ProgramID<N>,
        rng: &mut R,
    ) -> Result<Deployment<N>> {
        // Compute the deployment.
        self.get_stack(program_id)?.deploy::<A, R>(rng)
    }

    /// Verifies the given deployment is well-formed.
    #[inline]
    pub fn verify_deployment<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        deployment: &Deployment<N>,
        rng: &mut R,
    ) -> Result<()> {
        // Retrieve the edition.
        let edition = deployment.edition();
        // Retrieve the program.
        let program = deployment.program().clone();
        // Retrieve the program ID.
        let program_id = deployment.program().id();

        // Ensure the edition matches.
        ensure!(edition == N::EDITION, "Deployed the wrong edition (expected '{}', found '{edition}').", N::EDITION);
        // Ensure the program does not already exist in the process.
        ensure!(!self.contains_program(program_id), "Program '{program_id}' already exists");

        // Check Program //

        // Serialize the program into bytes.
        let program_bytes = program.to_bytes_le()?;
        // Ensure the program deserializes from bytes correctly.
        ensure!(program == Program::from_bytes_le(&program_bytes)?, "Program byte serialization failed");

        // Serialize the program into string.
        let program_string = program.to_string();
        // Ensure the program deserializes from a string correctly.
        ensure!(program == Program::from_str(&program_string)?, "Program string serialization failed");

        // Ensure the program is well-formed, by computing the stack.
        let stack = Stack::new(self, &program)?;

        // Check Certificates //

        // Ensure the verifying keys are well-formed and the certificates are valid.
        stack.verify_deployment::<A, R>(deployment.verifying_keys(), rng)?;

        Ok(())
    }
}
