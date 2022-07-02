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

// mod bytes;
mod to_fields;
mod to_trace;

use crate::{Identifier, ProgramID, StackValue, Trace, ValueType};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Clone)]
pub struct Request<N: Network> {
    /// The request caller.
    caller: Address<N>,
    /// The network ID.
    network_id: U16<N>,
    /// The program ID.
    program_id: ProgramID<N>,
    /// The function name.
    function_name: Identifier<N>,
    /// The function inputs.
    inputs: Vec<StackValue<N>>,
}

impl<N: Network> Request<N> {
    /// Initializes a new request.
    pub const fn new(
        caller: Address<N>,
        program_id: ProgramID<N>,
        function_name: Identifier<N>,
        inputs: Vec<StackValue<N>>,
    ) -> Self {
        Self { caller, network_id: U16::new(N::ID), program_id, function_name, inputs }
    }

    /// Returns the request caller.
    pub const fn caller(&self) -> &Address<N> {
        &self.caller
    }

    /// Returns the network ID.
    pub const fn network_id(&self) -> &U16<N> {
        &self.network_id
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }

    /// Returns the function inputs.
    pub fn inputs(&self) -> &[StackValue<N>] {
        &self.inputs
    }
}
