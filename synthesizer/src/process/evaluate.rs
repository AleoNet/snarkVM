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
        let timer = timer!("Process::evaluate");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Evaluating '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Evaluate the function.
        let response =
            self.get_stack(request.program_id())?.evaluate_function::<A>(CallStack::evaluate(authorization)?);
        lap!(timer, "Evaluate the function");

        finish!(timer);

        response
    }
}
