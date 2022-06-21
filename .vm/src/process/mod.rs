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

use crate::{Operand, Program, RegisterTypes, Stack, StackValue, Trace};
use console::{
    account::Address,
    network::prelude::*,
    program::{Entry, Identifier, Literal, Plaintext, Record, Register, RegisterType, Value, ValueType},
};

pub struct Process<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N, A>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Process<N, A> {
    /// Evaluates a program function on the given inputs.
    #[inline]
    pub fn evaluate(
        &self,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Evaluate the function.
        // Stack::<N, A>::evaluate(self.program.clone(), function_name, inputs)
        self.program.evaluate(function_name, inputs)
    }

    /// Executes a program function on the given inputs.
    #[inline]
    pub fn execute<R: Rng + CryptoRng>(
        &self,
        caller: Address<N>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
        rng: &mut R,
    ) -> Result<Vec<circuit::Value<A, circuit::Plaintext<A>>>> {
        // // Retrieve the function from the program.
        // let function = program.get_function(function_name)?;

        // // Initialize a new caller account.
        // let caller_private_key = PrivateKey::<<circuit::AleoV0 as circuit::Environment>::Network>::new(&mut rng)?;
        // let _caller_view_key = ViewKey::try_from(&caller_private_key)?;
        // let caller_address = Address::try_from(&caller_private_key)?;

        // Initialize the trace.
        let mut trace = Trace::new(caller, rng)?;

        // Execute the function.
        Stack::<N, A>::execute_transition(&mut trace, self.program.clone(), function_name, inputs)
        // self.program.execute(function_name, inputs)
    }
}
