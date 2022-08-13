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
    /// Deploys the given program ID, if it does not exist.
    #[inline]
    pub fn deploy<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        program: &Program<N>,
        rng: &mut R,
    ) -> Result<Deployment<N>> {
        // Compute the stack.
        let stack = Stack::new(self, program)?;
        // Return the deployment.
        stack.deploy::<A, R>(program, rng)
    }

    /// Verifies the given deployment is well-formed.
    #[inline]
    pub fn verify_deployment<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        deployment: &Deployment<N>,
        rng: &mut R,
    ) -> Result<()> {
        // Retrieve the program ID.
        let program_id = deployment.program().id();
        // Ensure the program does not already exist in the process.
        ensure!(!self.contains_program(program_id), "Program '{program_id}' already exists");

        // Ensure the program is well-formed, by computing the stack.
        let stack = Stack::new(self, deployment.program())?;
        // Ensure the verifying keys are well-formed and the certificates are valid.
        stack.verify_deployment::<A, R>(deployment, rng)
    }

    /// Adds the newly-deployed program.
    #[inline]
    pub fn finalize_deployment(&mut self, deployment: &Deployment<N>) -> Result<()> {
        // Add the program.
        self.add_program(deployment.program())?;
        // Insert the verifying keys.
        for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
            self.insert_verifying_key(deployment.program().id(), function_name, verifying_key.clone())?;
        }
        Ok(())
    }
}
