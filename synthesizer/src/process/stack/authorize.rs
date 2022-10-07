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
    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        // Ensure the program contains functions.
        ensure!(!self.program.functions().is_empty(), "Program '{}' has no transitions", self.program.id());

        // Retrieve the function.
        let function = self.get_function(&function_name)?;
        // Retrieve the input types.
        let input_types = function.input_types();
        // Ensure the number of inputs matches the number of input types.
        if function.inputs().len() != input_types.len() {
            bail!(
                "Transition '{function_name}' in program '{}' expects {} inputs, but {} types were found.",
                self.program.id(),
                function.inputs().len(),
                input_types.len()
            )
        }

        // Compute the request.
        let request = Request::sign(private_key, *self.program.id(), function_name, inputs, &input_types, rng)?;
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        // Construct the call stack.
        let call_stack = CallStack::Authorize(vec![request], *private_key, authorization.clone());
        // Construct the authorization from the function.
        let _response = self.execute_function::<A, R>(call_stack, rng)?;
        // Return the authorization.
        Ok(authorization)
    }
}
