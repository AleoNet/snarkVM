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

impl<N: Network> Stack<N> {
    /// Deploys the given program ID, if it does not exist.
    #[inline]
    pub fn deploy<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Deployment<N>> {
        // Ensure the program contains functions.
        ensure!(!self.program.functions().is_empty(), "Program '{}' has no transitions", self.program.id());

        // Initialize a mapping for the bundle.
        let mut bundle = IndexMap::with_capacity(self.program.functions().len());

        for function_name in self.program.functions().keys() {
            // Synthesize the proving and verifying key.
            self.synthesize_key::<A, R>(function_name, rng)?;

            // Retrieve the proving key.
            let proving_key = self.get_proving_key(function_name)?;
            // Retrieve the verifying key.
            let verifying_key = self.get_verifying_key(function_name)?;

            // Certify the circuit.
            let certificate = Certificate::certify(function_name, &proving_key, &verifying_key)?;

            // Add the verifying key and certificate to the bundle.
            bundle.insert(*function_name, (verifying_key, certificate));
        }

        // Return the deployment.
        Deployment::new(N::EDITION, self.program.clone(), bundle)
    }

    /// Checks each function in the program on the given verifying key and certificate.
    #[inline]
    pub fn verify_deployment<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        deployment: &Deployment<N>,
        rng: &mut R,
    ) -> Result<()> {
        // Retrieve the edition.
        let edition = deployment.edition();
        // Retrieve the program.
        let program = &self.program;
        // Retrieve the program ID.
        let program_id = program.id();
        // Retrieve the verifying keys.
        let verifying_keys = deployment.verifying_keys();

        // Sanity Checks //

        // Ensure the edition matches.
        ensure!(edition == N::EDITION, "Deployed the wrong edition (expected '{}', found '{edition}').", N::EDITION);
        // Ensure the program matches.
        ensure!(program == deployment.program(), "The stack program does not match the deployment program");
        // Ensure the program network-level domain (NLD) is correct.
        ensure!(program_id.is_aleo(), "Program '{program_id}' has an incorrect network-level domain (NLD)");
        // Ensure the program contains functions.
        ensure!(!program.functions().is_empty(), "No transitions present in the deployment for program '{program_id}'");
        // Ensure the deployment contains verifying keys.
        ensure!(!verifying_keys.is_empty(), "No verifying keys present in the deployment for program '{program_id}'");

        // Check Verifying Keys //

        // Ensure the number of verifying keys matches the number of program functions.
        if verifying_keys.len() != program.functions().len() {
            bail!("The number of verifying keys does not match the number of program transitions");
        }

        // Ensure the program functions are in the same order as the verifying keys.
        for ((function_name, function), candidate_name) in program.functions().iter().zip_eq(verifying_keys.keys()) {
            // Ensure the function name is correct.
            if function_name != function.name() {
                bail!("The transition key is '{function_name}', but the transition name is '{}'", function.name())
            }
            // Ensure the function name with the verifying key is correct.
            if candidate_name != function.name() {
                bail!("The verifier key is '{candidate_name}', but the transition name is '{}'", function.name())
            }
        }

        // Iterate through the program functions.
        for (function, (verifying_key, certificate)) in program.functions().values().zip_eq(verifying_keys.values()) {
            // Initialize a burner private key.
            let burner_private_key = PrivateKey::new(rng)?;
            // Compute the burner address.
            let burner_address = Address::try_from(&burner_private_key)?;
            // Retrieve the input types.
            let input_types = function.input_types();
            // Sample the inputs.
            let inputs = input_types
                .iter()
                .map(|input_type| match input_type {
                    ValueType::ExternalRecord(locator) => {
                        // Retrieve the external stack.
                        let stack = self.get_external_stack(locator.program_id())?;
                        // Sample the input.
                        stack.sample_value(&burner_address, &ValueType::Record(*locator.resource()), rng)
                    }
                    _ => self.sample_value(&burner_address, input_type, rng),
                })
                .collect::<Result<Vec<_>>>()?;

            // Compute the request, with a burner private key.
            let request =
                Request::sign(&burner_private_key, *program_id, *function.name(), &inputs, &input_types, rng)?;
            // Initialize the assignments.
            let assignments = Assignments::<N>::default();
            // Initialize the call stack.
            let call_stack = CallStack::CheckDeployment(vec![request], burner_private_key, assignments.clone());
            // Synthesize the circuit.
            let _response = self.execute_function::<A, R>(call_stack, rng)?;
            // Check the certificate.
            match assignments.read().last() {
                None => bail!("The assignment for transition '{}' is missing in '{program_id}'", function.name()),
                Some(assignment) => {
                    // Ensure the certificate is valid.
                    if !certificate.verify(function.name(), assignment, verifying_key) {
                        bail!("The certificate for transition '{}' is invalid in '{program_id}'", function.name())
                    }
                }
            };
        }

        Ok(())
    }
}
