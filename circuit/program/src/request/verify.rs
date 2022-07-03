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

impl<A: Aleo> Request<A> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_numbers == serial_numbers') where:
    ///     challenge' := HashToScalar(r * G, pk_sig, pr_sig, caller, \[tvk, function ID, input IDs\])
    pub fn verify(&self) -> Boolean<A> {
        // Compute the function ID as `Hash(network_id, program_id, function_name)`.
        let function_id = A::hash_bhp1024(
            &[
                self.network_id.to_bits_le(),
                self.program_id.name().to_bits_le(),
                self.program_id.network().to_bits_le(),
                self.function_name.to_bits_le(),
            ]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>(),
        );

        // Construct the signature message as `[tvk, function ID, input IDs]`.
        let mut message = Vec::with_capacity(1 + 2 * self.input_ids.len());
        message.push(self.tvk.clone());
        message.push(function_id);

        // Retrieve the challenge from the signature.
        let challenge = self.signature.challenge();
        // Retrieve the response from the signature.
        let response = self.signature.response();

        // Initialize an iterator for the input checks.
        let input_checks = self
            .input_ids
            .iter()
            .zip_eq(&self.inputs)
            .enumerate()
            .map(|(index, (input_id, input))| {
                match input_id {
                    // A constant input is hashed to a field element.
                    InputID::Constant(input_hash) => {
                        // Add the input hash to the message.
                        message.push(input_hash.clone());
                        // Ensure the expected hash matches the computed hash.
                        input_hash.is_equal(&A::hash_bhp1024(&input.to_bits_le()))
                    }
                    // A public input is hashed to a field element.
                    InputID::Public(input_hash) => {
                        // Add the input hash to the message.
                        message.push(input_hash.clone());
                        // Ensure the expected hash matches the computed hash.
                        input_hash.is_equal(&A::hash_bhp1024(&input.to_bits_le()))
                    }
                    // A private input is encrypted (using `tvk`) and hashed to a field element.
                    InputID::Private(input_hash) => {
                        // Add the input hash to the message.
                        message.push(input_hash.clone());

                        // Prepare the index as a constant field element.
                        let input_index = Field::constant(console::Field::from_u16(index as u16));
                        // Compute the input view key as `Hash(tvk || index)`.
                        let input_view_key = A::hash_psd2(&[self.tvk.clone(), input_index]);
                        // Compute the ciphertext.
                        let ciphertext = match &input {
                            Value::Plaintext(plaintext) => plaintext.encrypt_symmetric(input_view_key),
                            // Ensure the input is a plaintext.
                            Value::Record(..) => A::halt("Expected a plaintext input, found a record input"),
                        };
                        // Ensure the expected hash matches the computed hash.
                        input_hash.is_equal(&A::hash_bhp1024(&ciphertext.to_bits_le()))
                    }
                    // An input record is computed to its serial number.
                    InputID::Record(gamma, serial_number) => {
                        // Prepare the index as a constant field element.
                        let input_index = Field::constant(console::Field::from_u16(index as u16));
                        // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                        let randomizer = A::hash_to_scalar_psd2(&[self.tvk.clone(), input_index]);
                        // Compute the record commitment.
                        let commitment = match &input {
                            Value::Record(record) => record.to_commitment(&randomizer),
                            // Ensure the input is a record.
                            Value::Plaintext(..) => A::halt("Expected a record input, found a plaintext input"),
                        };
                        // Compute the generator `H` as `HashToGroup(commitment)`.
                        let h = A::hash_to_group_psd2(&[A::serial_number_domain(), commitment.clone()]);
                        // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
                        let h_r = (gamma * challenge) + (&h * response);
                        // Add `H`, `r * H`, and `gamma` to the message.
                        message.extend([h, h_r, gamma.clone()].iter().map(|point| point.to_x_coordinate()));

                        // Compute `sn_nonce` as `HashToScalar(COFACTOR * gamma)`.
                        let sn_nonce = A::hash_to_scalar_psd2(&[
                            A::serial_number_domain(),
                            gamma.mul_by_cofactor().to_x_coordinate(),
                        ]);
                        // Compute `candidate_serial_number` as `Commit(commitment, serial_number_nonce)`.
                        let candidate_serial_number =
                            A::commit_bhp512(&(A::serial_number_domain(), commitment).to_bits_le(), &sn_nonce);

                        // Ensure the candidate serial number matches the expected serial number.
                        serial_number.is_equal(&candidate_serial_number)
                    }
                }
            })
            .fold(Boolean::constant(true), |acc, x| acc & x);

        // Verify the signature and serial numbers are valid.
        self.signature.verify(&self.caller, &message) & input_checks
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::test_crypto_rng;

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 50;

    fn check_verify(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        let rng = &mut test_crypto_rng();

        for i in 0..ITERATIONS {
            // Sample a random private key.
            let private_key = snarkvm_console_account::PrivateKey::<<Circuit as Environment>::Network>::new(rng)?;

            // Construct a program ID and function name.
            let program_id = console::ProgramID::from_str("token.aleo")?;
            let function_name = console::Identifier::from_str("transfer")?;

            // Construct four inputs.
            let input_constant = console::Value::<<Circuit as Environment>::Network>::Plaintext(
                console::Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap(),
            );
            let input_public = console::Value::<<Circuit as Environment>::Network>::Plaintext(
                console::Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap(),
            );
            let input_private = console::Value::<<Circuit as Environment>::Network>::Plaintext(
                console::Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap(),
            );
            let input_record = console::Value::<<Circuit as Environment>::Network>::Record(console::Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap());
            let inputs = vec![input_constant, input_public, input_private, input_record];

            // Construct the input types.
            let input_types = vec![
                console::ValueType::from_str("amount.constant").unwrap(),
                console::ValueType::from_str("amount.public").unwrap(),
                console::ValueType::from_str("amount.private").unwrap(),
                console::ValueType::from_str("token.record").unwrap(),
            ];

            // Compute the signed request.
            let request = console::Request::sign(&private_key, program_id, function_name, inputs, &input_types, rng)?;
            assert!(request.verify());

            // Inject the request into a circuit.
            let request = Request::<Circuit>::new(mode, request);

            Circuit::scope(format!("Request {i}"), || {
                let candidate = request.verify();
                assert!(candidate.eject_value());
                match mode.is_constant() {
                    true => assert_scope!(<=num_constants, <=num_public, <=num_private, <=num_constraints),
                    false => assert_scope!(<=num_constants, num_public, num_private, num_constraints),
                }
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_sign_and_verify_constant() -> Result<()> {
        // Note: This is correct. At this (high) level of a program, we override the default mode in the `Record` case,
        // based on the user-defined visibility in the record type. Thus, we have nonzero private and constraint values.
        check_verify(Mode::Constant, 37400, 0, 13600, 13600)
    }

    #[test]
    fn test_sign_and_verify_public() -> Result<()> {
        check_verify(Mode::Public, 33557, 0, 26663, 26697)
    }

    #[test]
    fn test_sign_and_verify_private() -> Result<()> {
        check_verify(Mode::Private, 33557, 0, 26663, 26697)
    }
}
