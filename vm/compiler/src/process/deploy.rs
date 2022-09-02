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
        stack.deploy::<A, R>(rng)
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

    /// Finalizes the deployment.
    /// This method assumes the given deployment **is valid**.
    #[inline]
    pub fn finalize_deployment<P: ProgramStorage<N>>(
        &mut self,
        store: &ProgramStore<N, P>,
        deployment: &Deployment<N>,
    ) -> Result<()> {
        // TODO (howardwu): Make this function atomic.
        // TODO (howardwu): Check the program ID and all mappings don't exist in the 'store'. (add this to verify_deployment too)

        // Compute the program stack.
        let stack = Stack::new(self, deployment.program())?;
        // Insert the verifying keys.
        for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
            stack.insert_verifying_key(function_name, verifying_key.clone())?;
        }

        // Retrieve the program ID.
        let program_id = deployment.program_id();
        // Iterate through the program mappings.
        for mapping in deployment.program().mappings().values() {
            store.initialize_mapping(program_id, mapping.name())?;
        }

        // Add the stack to the process.
        self.stacks.insert(*deployment.program_id(), stack);
        Ok(())
    }

    /// Adds the newly-deployed program.
    /// This method assumes the given deployment **is valid**.
    #[inline]
    pub(crate) fn load_deployment(&mut self, deployment: &Deployment<N>) -> Result<()> {
        // Compute the program stack.
        let stack = Stack::new(self, deployment.program())?;
        // Insert the verifying keys.
        for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
            stack.insert_verifying_key(function_name, verifying_key.clone())?;
        }
        // Add the stack to the process.
        self.stacks.insert(*deployment.program_id(), stack);
        Ok(())
    }
}
