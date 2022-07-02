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

mod to_fields;

use crate::{CircuitValue, Identifier, ProgramID};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Field, U16};

#[derive(Clone)]
pub struct Request<A: Aleo> {
    /// The request caller.
    caller: Address<A>,
    /// The network ID.
    network_id: U16<A>,
    /// The program ID.
    program_id: ProgramID<A>,
    /// The function name.
    function_name: Identifier<A>,
    /// The function inputs.
    inputs: Vec<CircuitValue<A>>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Request<A> {
    type Primitive = console::Request<A::Network>;

    /// Initializes a new request.
    fn new(mode: Mode, request: Self::Primitive) -> Self {
        Self {
            caller: Address::new(mode, *request.caller()),
            network_id: U16::new(mode, *request.network_id()),
            program_id: ProgramID::new(mode, *request.program_id()),
            function_name: Identifier::new(mode, *request.function_name()),
            inputs: request.inputs().iter().map(|input| CircuitValue::new(mode, input.clone())).collect(),
        }
    }
}

impl<A: Aleo> Request<A> {
    /// Returns the request caller.
    pub const fn caller(&self) -> &Address<A> {
        &self.caller
    }

    /// Returns the network ID.
    pub const fn network_id(&self) -> &U16<A> {
        &self.network_id
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<A> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<A> {
        &self.function_name
    }

    /// Returns the function inputs.
    pub fn inputs(&self) -> &[CircuitValue<A>] {
        &self.inputs
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Request<A> {
    type Primitive = console::Request<A::Network>;

    /// Ejects the mode of the request.
    fn eject_mode(&self) -> Mode {
        Mode::combine(self.caller.eject_mode(), [
            self.network_id.eject_mode(),
            self.program_id.eject_mode(),
            self.function_name.eject_mode(),
            self.inputs.eject_mode(),
        ])
    }

    /// Ejects the request as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        console::Request::new(
            self.caller.eject_value(),
            *self.network_id.eject_value(),
            self.program_id.eject_value(),
            self.function_name.eject_value(),
            self.inputs.eject_value(),
        )
    }
}
