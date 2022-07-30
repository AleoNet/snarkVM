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
    pub fn evaluate<A: circuit::Aleo<Network = N>>(&self, request: &Request<N>) -> Result<Response<N>> {
        // Retrieve the program, function, and input types.
        let (program, function, input_types, output_types) =
            self.get_function_info(request.program_id(), request.function_name())?;

        // Ensure the request is well-formed.
        ensure!(request.verify(&input_types), "Request is invalid");

        // Prepare the stack.
        let stack = self.get_stack(program.id())?;
        // Evaluate the function.
        let outputs = stack.evaluate_function::<A>(&function, request.inputs())?;
        // Compute the response.
        let response = Response::new(program.id(), request.inputs().len(), request.tvk(), outputs, &output_types)?;

        Ok(response)
    }
}
