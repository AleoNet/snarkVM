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

mod input_id;
pub use input_id::InputID;

mod bytes;
mod serialize;
mod sign;
mod string;
mod verify;

use crate::{Identifier, ProgramID, Value, ValueType};
use snarkvm_console_account::{Address, ComputeKey, PrivateKey, Signature};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Clone, PartialEq, Eq)]
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
    /// The transition secret key.
    tsk: Scalar<N>,
}

impl<N: Network>
    From<(
        Address<N>,
        U16<N>,
        ProgramID<N>,
        Identifier<N>,
        Vec<InputID<N>>,
        Vec<Value<N>>,
        Signature<N>,
        Field<N>,
        Scalar<N>,
    )> for Request<N>
{
    /// Note: See `Request::sign` to create the request. This method is used to eject from a circuit.
    fn from(
        (caller, network_id, program_id, function_name, input_ids, inputs, signature, tvk, tsk): (
            Address<N>,
            U16<N>,
            ProgramID<N>,
            Identifier<N>,
            Vec<InputID<N>>,
            Vec<Value<N>>,
            Signature<N>,
            Field<N>,
            Scalar<N>,
        ),
    ) -> Self {
        // Ensure the network ID is correct.
        if *network_id != N::ID {
            N::halt(format!("Invalid network ID. Expected {}, found {}", N::ID, *network_id))
        } else {
            Self { caller, network_id, program_id, function_name, input_ids, inputs, signature, tvk, tsk }
        }
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

    /// Returns the transition secret key `tsk`.
    pub const fn tsk(&self) -> &Scalar<N> {
        &self.tsk
    }
}

#[cfg(test)]
mod test_helpers {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    pub(super) fn sample_requests() -> Vec<Request<CurrentNetwork>> {
        let rng = &mut test_crypto_rng();

        (0..ITERATIONS)
            .map(|i| {
                // Sample a random private key and address.
                let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
                let address = Address::try_from(&private_key).unwrap();

                // Construct a program ID and function name.
                let program_id = ProgramID::from_str("token.aleo").unwrap();
                let function_name = Identifier::from_str("transfer").unwrap();

                // Prepare a record belonging to the address.
                let record_string =
                    format!("{{ owner: {address}.private, gates: {i}u64.private, token_amount: {i}u64.private }}");

                // Construct four inputs.
                let input_constant = Value::from_str(&format!("{{ token_amount: {i}u128 }}")).unwrap();
                let input_public = Value::from_str(&format!("{{ token_amount: {i}u128 }}")).unwrap();
                let input_private = Value::from_str(&format!("{{ token_amount: {i}u128 }}")).unwrap();
                let input_record = Value::from_str(&record_string).unwrap();
                let input_external_record = Value::from_str(&record_string).unwrap();
                let inputs = vec![input_constant, input_public, input_private, input_record, input_external_record];

                // Construct the input types.
                let input_types = vec![
                    ValueType::from_str("amount.constant").unwrap(),
                    ValueType::from_str("amount.public").unwrap(),
                    ValueType::from_str("amount.private").unwrap(),
                    ValueType::from_str("token.record").unwrap(),
                    ValueType::from_str("token.aleo/token.record").unwrap(),
                ];

                // Compute the signed request.
                let request =
                    Request::sign(&private_key, program_id, function_name, &inputs, &input_types, rng).unwrap();
                assert!(request.verify(&input_types));
                request
            })
            .collect()
    }
}
