// Copyright (C) 2019-2023 Aleo Systems Inc.
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
        let timer = timer!("Process::deploy");

        // Compute the stack.
        let stack = Stack::new(self, program)?;
        lap!(timer, "Compute the stack");

        // Return the deployment.
        let deployment = stack.deploy::<A, R>(rng);
        lap!(timer, "Construct the deployment");

        finish!(timer);

        deployment
    }

    /// Verifies the given deployment is ordered.
    #[inline]
    pub fn verify_deployment<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        deployment: &Deployment<N>,
        rng: &mut R,
    ) -> Result<()> {
        let timer = timer!("Process::verify_deployment");
        // Retrieve the program ID.
        let program_id = deployment.program().id();
        // Ensure the program does not already exist in the process.
        ensure!(!self.contains_program(program_id), "Program '{program_id}' already exists");
        // Ensure the program is well-formed, by computing the stack.
        let stack = Stack::new(self, deployment.program())?;
        lap!(timer, "Compute the stack");

        // Ensure the verifying keys are well-formed and the certificates are valid.
        let verification = stack.verify_deployment::<A, R>(deployment, rng);
        lap!(timer, "Verify the deployment");

        finish!(timer);

        verification
    }

    /// Adds the newly-deployed program.
    /// This method assumes the given deployment **is valid**.
    #[inline]
    pub fn load_deployment(&mut self, deployment: &Deployment<N>) -> Result<()> {
        let timer = timer!("Process::load_deployment");

        // Compute the program stack.
        let stack = Stack::new(self, deployment.program())?;
        lap!(timer, "Compute the stack");

        // Insert the verifying keys.
        for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
            stack.insert_verifying_key(function_name, verifying_key.clone())?;
        }
        lap!(timer, "Insert the verifying keys");

        // Add the stack to the process.
        self.add_stack(stack);

        finish!(timer);

        Ok(())
    }
}
