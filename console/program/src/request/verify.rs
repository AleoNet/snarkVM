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

impl<N: Network> Request<N> {
    /// Returns `true` if the request is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_numbers == serial_numbers') where:
    ///     challenge' := HashToScalar(r * G, pk_sig, pr_sig, caller, \[tvk, input IDs\])
    pub fn verify(&self, input_types: &[ValueType<N>]) -> bool {
        // Verify the transition public key and transition view key are well-formed.
        {
            // Compute the transition public key `tpk` as `tsk * G`.
            let tpk = N::g_scalar_multiply(&self.tsk);
            // Ensure the transition public key matches with the derived one from the signature.
            if tpk != self.to_tpk() {
                eprintln!("Invalid transition public key in request.");
                return false;
            }

            // Compute the transition view key `tvk` as `tsk * caller`.
            let tvk = (*self.caller * self.tsk).to_x_coordinate();
            // Ensure the computed transition view key matches.
            if tvk != self.tvk {
                eprintln!("Invalid transition view key in request.");
                return false;
            }
        }

        // Compute the function ID as `Hash(network_id, program_id, function_name)`.
        let function_id = match N::hash_bhp1024(
            &[
                U16::<N>::new(N::ID).to_bits_le(),
                self.program_id.name().to_bits_le(),
                self.program_id.network().to_bits_le(),
                self.function_name.to_bits_le(),
            ]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>(),
        ) {
            Ok(function_id) => function_id,
            Err(error) => {
                eprintln!("Failed to construct the function ID: {error}");
                return false;
            }
        };

        // Construct the signature message as `[tvk, function ID, input IDs]`.
        let mut message = Vec::with_capacity(1 + self.input_ids.len());
        message.push(self.tvk);
        message.push(function_id);

        // Retrieve the challenge from the signature.
        let challenge = self.signature.challenge();
        // Retrieve the response from the signature.
        let response = self.signature.response();

        if let Err(error) = self.input_ids.iter().zip_eq(&self.inputs).zip_eq(input_types).enumerate().try_for_each(
            |(index, ((input_id, input), input_type))| {
                match input_id {
                    // A constant input is hashed to a field element.
                    InputID::Constant(input_hash) => {
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                        // Hash the input to a field element.
                        let candidate_hash = N::hash_bhp1024(&input.to_bits_le())?;
                        // Ensure the input hash matches.
                        ensure!(*input_hash == candidate_hash, "Expected a constant input with the same hash");
                        // Add the input hash to the message.
                        message.push(candidate_hash);
                    }
                    // A public input is hashed to a field element.
                    InputID::Public(input_hash) => {
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                        // Hash the input to a field element.
                        let candidate_hash = N::hash_bhp1024(&input.to_bits_le())?;
                        // Ensure the input hash matches.
                        ensure!(*input_hash == candidate_hash, "Expected a public input with the same hash");
                        // Add the input hash to the message.
                        message.push(candidate_hash);
                    }
                    // A private input is encrypted (using `tvk`) and hashed to a field element.
                    InputID::Private(input_hash) => {
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                        // Prepare the index as a constant field element.
                        let index = Field::from_u16(index as u16);
                        // Compute the input view key as `Hash(tvk || index)`.
                        let input_view_key = N::hash_psd2(&[self.tvk, index])?;
                        // Compute the ciphertext.
                        let ciphertext = match &input {
                            Value::Plaintext(plaintext) => plaintext.encrypt_symmetric(input_view_key)?,
                            // Ensure the input is a plaintext.
                            Value::Record(..) => bail!("Expected a plaintext input, found a record input"),
                        };
                        // Hash the ciphertext to a field element.
                        let candidate_hash = N::hash_bhp1024(&ciphertext.to_bits_le())?;
                        // Ensure the input hash matches.
                        ensure!(*input_hash == candidate_hash, "Expected a private input with the same commitment");
                        // Add the input hash to the message.
                        message.push(candidate_hash);
                    }
                    // A record input is computed to its serial number.
                    InputID::Record(gamma, serial_number) => {
                        // Prepare the index as a constant field element.
                        let index = Field::from_u16(index as u16);
                        // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                        let randomizer = N::hash_to_scalar_psd2(&[self.tvk, index])?;
                        // Retrieve the record.
                        let record = match &input {
                            Value::Record(record) => record,
                            // Ensure the input is a record.
                            Value::Plaintext(..) => bail!("Expected a record input, found a plaintext input"),
                        };
                        // Retrieve the record name.
                        let record_name = match input_type {
                            ValueType::Record(record_name) => record_name,
                            // Ensure the input type is a record.
                            _ => bail!("Expected a record type at input {index}"),
                        };
                        // Compute the record commitment.
                        let commitment = record.to_commitment(&self.program_id, record_name, &randomizer)?;
                        // Ensure the record belongs to the caller.
                        ensure!(**record.owner() == self.caller, "Input record does not belong to the caller");
                        // Ensure the record gates is less than or equal to 2^52.
                        if !(**record.gates()).to_bits_le()[52..].iter().all(|bit| !bit) {
                            bail!("Input record contains an invalid Aleo balance (in gates): {}", record.gates());
                        }

                        // Compute the generator `H` as `HashToGroup(commitment)`.
                        let h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;
                        // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
                        let h_r = (*gamma * challenge) + (h * response);
                        // Add `H`, `r * H`, and `gamma` to the message.
                        message.extend([h, h_r, *gamma].iter().map(|point| point.to_x_coordinate()));

                        // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
                        let sn_nonce = N::hash_to_scalar_psd2(&[
                            N::serial_number_domain(),
                            gamma.mul_by_cofactor().to_x_coordinate(),
                        ])?;
                        // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
                        let candidate_sn =
                            N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)?;
                        // Ensure the serial number matches.
                        ensure!(*serial_number == candidate_sn, "Expected a record input with the same serial number");
                    }
                    // An external record input is committed (using `tvk`) to a field element.
                    InputID::ExternalRecord(input_commitment) => {
                        // Ensure the input is a record.
                        ensure!(matches!(input, Value::Record(..)), "Expected a record input");
                        // Construct the (console) input index as a field element.
                        let index = Field::from_u16(index as u16);
                        // Compute the input randomizer as `HashToScalar(tvk || index)`.
                        let input_randomizer = N::hash_to_scalar_psd2(&[self.tvk, index])?;
                        // Commit to the input to a field element.
                        let candidate_cm = N::commit_bhp1024(&input.to_bits_le(), &input_randomizer)?;
                        // Ensure the input commitment matches.
                        ensure!(*input_commitment == candidate_cm, "Expected a locator input with the same commitment");
                        // Add the input commitment to the message.
                        message.push(candidate_cm);
                    }
                }
                Ok(())
            },
        ) {
            eprintln!("Request verification failed on input checks: {error}");
            return false;
        }

        // Verify the signature.
        self.signature.verify(&self.caller, &message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_account::PrivateKey;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(crate) const ITERATIONS: usize = 1000;

    #[test]
    fn test_sign_and_verify() {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Sample a random private key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
            let address = Address::try_from(&private_key).unwrap();

            // Construct a program ID and function name.
            let program_id = ProgramID::from_str("token.aleo").unwrap();
            let function_name = Identifier::from_str("transfer").unwrap();

            // Prepare a record belonging to the address.
            let record_string =
                format!("{{ owner: {address}.private, gates: 5u64.private, token_amount: 100u64.private }}");

            // Construct four inputs.
            let input_constant = Value::from_str("{ token_amount: 9876543210u128 }").unwrap();
            let input_public = Value::from_str("{ token_amount: 9876543210u128 }").unwrap();
            let input_private = Value::from_str("{ token_amount: 9876543210u128 }").unwrap();
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
            let request = Request::sign(&private_key, program_id, function_name, &inputs, &input_types, rng).unwrap();
            assert!(request.verify(&input_types));
        }
    }
}
