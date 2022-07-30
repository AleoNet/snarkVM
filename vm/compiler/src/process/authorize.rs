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
    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: &ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        // Retrieve the program, function, and input types.
        let (program, function, input_types, _) = self.get_function_info(program_id, &function_name)?;
        // Compute the request.
        let request = Request::sign(private_key, *program.id(), *function.name(), inputs, &input_types, rng)?;
        // Initialize the authorization.
        let authorization = Authorization::new(&[request.clone()]);
        // Construct the authorization from the function.
        let _response = self
            .get_stack(program.id())?
            .execute_function::<A, R>(CallStack::Authorize(vec![request], *private_key, authorization.clone()), rng)?;
        // Return the authorization.
        Ok(authorization)
    }
}
