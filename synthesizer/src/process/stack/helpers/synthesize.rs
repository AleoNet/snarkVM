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
    /// Synthesizes the proving key and verifying key for the given function name.
    #[inline]
    pub fn synthesize_key<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        function_name: &Identifier<N>,
        rng: &mut R,
    ) -> Result<()> {
        // If the proving and verifying key already exist, skip the synthesis for this function.
        if self.contains_proving_key(function_name) && self.contains_verifying_key(function_name) {
            return Ok(());
        }

        // Retrieve the program ID.
        let program_id = self.program_id();
        // Retrieve the function input types.
        let input_types = self.get_function(function_name)?.input_types();

        // Initialize a burner private key.
        let burner_private_key = PrivateKey::new(rng)?;
        // Compute the burner address.
        let burner_address = Address::try_from(&burner_private_key)?;
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
            Request::sign(&burner_private_key, *program_id, *function_name, inputs.into_iter(), &input_types, rng)?;
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        // Initialize the call stack.
        let call_stack = CallStack::Synthesize(vec![request], burner_private_key, authorization);
        // Synthesize the circuit.
        let _response = self.execute_function::<A, R>(call_stack, rng)?;

        // Ensure the proving key exists.
        ensure!(self.contains_proving_key(function_name), "Function '{function_name}' is missing a proving key.");
        // Ensure the verifying key exists.
        ensure!(self.contains_verifying_key(function_name), "Function '{function_name}' is missing a verifying key.");
        Ok(())
    }

    /// Synthesizes and stores the `(proving_key, verifying_key)` for the given function name and assignment.
    #[inline]
    pub fn synthesize_from_assignment(
        &self,
        function_name: &Identifier<N>,
        assignment: &circuit::Assignment<N::Field>,
    ) -> Result<()> {
        // If the proving and verifying key already exist, skip the synthesis for this function.
        if self.contains_proving_key(function_name) && self.contains_verifying_key(function_name) {
            return Ok(());
        }

        // Synthesize the proving and verifying key.
        let (proving_key, verifying_key) = self.universal_srs.to_circuit_key(function_name, assignment)?;
        // Insert the proving key.
        self.insert_proving_key(function_name, proving_key)?;
        // Insert the verifying key.
        self.insert_verifying_key(function_name, verifying_key)
    }
}
