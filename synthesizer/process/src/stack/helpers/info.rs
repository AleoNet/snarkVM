// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Stack<N> {
    /// Returns information about the given function.
    #[inline]
    pub fn info<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        function_name: &Identifier<N>,
        rng: &mut R,
    ) -> Result<A::Transcript> {
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
        
        // Compute the request, with a burner private key, root_tvk of None, and is_root of false.
        let request =
            Request::sign(&burner_private_key, *program_id, *function_name, inputs.into_iter(), &input_types, None, false, rng)?;
        // Initialize the authorization.
        let authorization = Authorization::new(request.clone());
        // Initialize the call stack.
        let call_stack = CallStack::Synthesize(vec![request], burner_private_key, authorization);
        // Synthesize the circuit.
        let _ = self.execute_function::<A, R>(call_stack, None, None, rng)?;

        let transcript = A::clear();

        Ok(transcript)
    }
}
