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
mod sign;
mod verify;

use crate::{Identifier, ProgramID, Value, ValueType};
use snarkvm_console_account::{Address, ComputeKey, PrivateKey, Signature};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum InputID<N: Network> {
    /// The hash of the constant input.
    Constant(Field<N>),
    /// The hash of the public input.
    Public(Field<N>),
    /// The ciphertext hash of the private input.
    Private(Field<N>),
    /// The gamma value and serial number of the record input.
    Record(Group<N>, Field<N>),
    /// The commitment of the external record input.
    ExternalRecord(Field<N>),
}

#[derive(Clone, Debug)]
pub struct Request<N: Network> {
    /// The request caller.
    caller: Address<N>,
    /// The network ID.
    network_id: U16<N>,
    /// The program ID.
    program_id: ProgramID<N>,
    /// The function name.
    function_name: Identifier<N>,
    /// The input ID for the transition.
    input_ids: Vec<InputID<N>>,
    /// The function inputs.
    inputs: Vec<Value<N>>,
    /// The signature for the transition.
    signature: Signature<N>,
    /// The transition view key.
    tvk: Field<N>,
}

impl<N: Network>
    From<(Address<N>, U16<N>, ProgramID<N>, Identifier<N>, Vec<InputID<N>>, Vec<Value<N>>, Signature<N>, Field<N>)>
    for Request<N>
{
    /// Note: See `Request::sign` to create the request. This method is used to eject from a circuit.
    fn from(
        (caller, network_id, program_id, function_name, input_ids, inputs, signature, tvk): (
            Address<N>,
            U16<N>,
            ProgramID<N>,
            Identifier<N>,
            Vec<InputID<N>>,
            Vec<Value<N>>,
            Signature<N>,
            Field<N>,
        ),
    ) -> Self {
        Self { caller, network_id, program_id, function_name, input_ids, inputs, signature, tvk }
    }
}

impl<N: Network> Request<N> {
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

    /// Returns the input ID for the transition.
    pub fn input_ids(&self) -> &[InputID<N>] {
        &self.input_ids
    }

    /// Returns the function inputs.
    pub fn inputs(&self) -> &[Value<N>] {
        &self.inputs
    }

    /// Returns the signature for the transition.
    pub const fn signature(&self) -> &Signature<N> {
        &self.signature
    }

    /// Returns the transition view key `tvk`.
    pub const fn tvk(&self) -> &Field<N> {
        &self.tvk
    }

    /// Returns the transition public key `tpk`.
    pub fn to_tpk(&self) -> Group<N> {
        // Retrieve the challenge from the signature.
        let challenge = self.signature.challenge();
        // Retrieve the response from the signature.
        let response = self.signature.response();
        // Retrieve `pk_sig` from the signature.
        let pk_sig = self.signature.compute_key().pk_sig();
        // Compute `tpk` as `(challenge * pk_sig) + (response * G)`, equivalent to `r * G`.
        (pk_sig * challenge) + N::g_scalar_multiply(&response)
    }
}
