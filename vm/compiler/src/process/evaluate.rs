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
    /// Evaluates a program function on the given request.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(&self, authorization: Authorization<N>) -> Result<Response<N>> {
        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Prepare the stack.
        let stack = self.get_stack(request.program_id())?;

        // Ensure the network ID matches.
        ensure!(
            **request.network_id() == N::ID,
            "Network ID mismatch. Expected {}, but found {}",
            N::ID,
            request.network_id()
        );
        // Ensure that the function exists.
        if !stack.program().contains_function(request.function_name()) {
            bail!("Function '{}' does not exist.", request.function_name())
        }

        println!("{}", format!(" • Evaluating '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Evaluate the function.
        let response = stack.evaluate_function::<A>(CallStack::evaluate(authorization)?)?;
        // Return the response.
        Ok(response)
    }
}
