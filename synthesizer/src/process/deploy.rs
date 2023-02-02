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

    /// Verifies the given deployment is well-formed.
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

    /// Finalizes the deployment.
    /// This method assumes the given deployment **is valid**.
    #[inline]
    pub fn finalize_deployment<P: ProgramStorage<N>>(
        &mut self,
        store: &ProgramStore<N, P>,
        deployment: &Deployment<N>,
    ) -> Result<()> {
        let timer = timer!("Process::finalize_deployment");

        // TODO (howardwu): Make this function atomic.
        // TODO (howardwu): Check the program ID and all mappings don't exist in the 'store'. (add this to verify_deployment too)

        // Compute the program stack.
        let stack = Stack::new(self, deployment.program())?;
        lap!(timer, "Compute the stack");

        // Insert the verifying keys.
        for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
            stack.insert_verifying_key(function_name, verifying_key.clone())?;
        }
        lap!(timer, "Insert the verifying keys");

        // Retrieve the program ID.
        let program_id = deployment.program_id();
        // Iterate through the program mappings.
        for mapping in deployment.program().mappings().values() {
            store.initialize_mapping(program_id, mapping.name())?;
        }
        lap!(timer, "Initialize the program mappings");

        // Add the stack to the process.
        self.stacks.insert(*deployment.program_id(), stack);

        finish!(timer);

        Ok(())
    }

    /// Adds the newly-deployed program.
    /// This method assumes the given deployment **is valid**.
    #[inline]
    pub(crate) fn load_deployment(&mut self, deployment: &Deployment<N>) -> Result<()> {
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
        self.stacks.insert(*deployment.program_id(), stack);

        finish!(timer);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    type CurrentAleo = circuit::network::AleoV0;

    #[test]
    fn test_finalize_deployment() {
        let rng = &mut TestRng::default();

        // Fetch the program from the deployment.
        let program = crate::vm::test_helpers::sample_program();
        // Initialize a new process.
        let mut process = Process::load().unwrap();
        // Deploy the program.
        let deployment = process.deploy::<CurrentAleo, _>(&program, rng).unwrap();

        // Initialize a new VM.
        let vm = crate::vm::test_helpers::sample_vm();

        // Ensure the program does not exist.
        assert!(!process.contains_program(program.id()));
        // Finalize the deployment.
        process.finalize_deployment(vm.program_store(), &deployment).unwrap();
        // Ensure the program exists.
        assert!(process.contains_program(program.id()));
    }
}
