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

mod sign;
mod verify;

use crate::{Identifier, ProgramID, Request, StackValue, ValueType};
use snarkvm_console_account::{Address, ComputeKey, Signature};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum InputID<N: Network> {
    /// The hash of the constant input.
    Constant(Field<N>),
    /// The hash of the public input.
    Public(Field<N>),
    /// The index and commitment of the private input.
    Private(Field<N>, Field<N>),
    /// The `(commitment, H, r * H, gamma, serial_number)` tuple of the record input.
    Record(Field<N>, Group<N>, Group<N>, Group<N>, Field<N>),
}

impl<N: Network> ToFields for InputID<N> {
    type Field = Field<N>;

    /// Returns the input as a list of field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        match self {
            InputID::Constant(field) => Ok(vec![*field]),
            InputID::Public(field) => Ok(vec![*field]),
            InputID::Private(index, field) => Ok(vec![*index, *field]),
            InputID::Record(commitment, h, h_r, gamma, serial_number) => Ok(vec![
                *commitment,
                h.to_x_coordinate(),
                h_r.to_x_coordinate(),
                gamma.to_x_coordinate(),
                *serial_number,
            ]),
        }
    }
}

// #[derive(Copy, Clone, PartialEq, Eq, Hash)]
// pub enum OutputID<N: Network> {
//     /// The hash of the constant output.
//     Constant(Field<N>),
//     /// The hash of the public output.
//     Public(Field<N>),
//     /// The commitment of the private output.
//     Private(Field<N>),
//     /// The commitment of the record output.
//     Record(Field<N>),
// }

#[derive(Clone, PartialEq, Eq)]
pub struct Call<N: Network> {
    /// The caller for the transition.
    caller: Address<N>,
    /// The program ID for the transition.
    program_id: ProgramID<N>,
    /// The function name for the transition.
    function_name: Identifier<N>,
    /// The input ID for the transition.
    input_ids: Vec<InputID<N>>,
    /// The function inputs.
    inputs: Vec<StackValue<N>>,
    /// The signature for the transition.
    signature: Signature<N>,
    /// The transition view key.
    tvk: Field<N>,
}

impl<N: Network>
    From<(Address<N>, ProgramID<N>, Identifier<N>, Vec<InputID<N>>, Vec<StackValue<N>>, Signature<N>, Field<N>)>
    for Call<N>
{
    /// Note: See `Call::sign` to create the call. This method is used to eject from a circuit.
    fn from(
        (caller, program_id, function_name, input_ids, inputs, signature, tvk): (
            Address<N>,
            ProgramID<N>,
            Identifier<N>,
            Vec<InputID<N>>,
            Vec<StackValue<N>>,
            Signature<N>,
            Field<N>,
        ),
    ) -> Self {
        Self { caller, program_id, function_name, input_ids, inputs, signature, tvk }
    }
}

impl<N: Network> Call<N> {
    /// Returns the caller for the transition.
    pub const fn caller(&self) -> &Address<N> {
        &self.caller
    }

    /// Returns the program ID for the transition.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the function name for the transition.
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }

    /// Returns the input ID for the transition.
    pub fn input_ids(&self) -> &[InputID<N>] {
        &self.input_ids
    }

    /// Returns the function inputs.
    pub fn inputs(&self) -> &[StackValue<N>] {
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
