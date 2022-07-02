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
    pub fn verify(&self) -> bool {
        // Construct the input IDs as field elements.
        let input_ids = match self.input_ids.iter().map(|input| input.to_fields()).collect::<Result<Vec<_>>>() {
            Ok(input_ids) => input_ids,
            Err(error) => {
                eprintln!("Failed to construct the input IDs: {error}");
                return false;
            }
        };

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
        let mut message = Vec::with_capacity(1 + input_ids.len());
        message.push(self.tvk);
        message.push(function_id);
        message.extend(input_ids.into_iter().flatten());

        // Retrieve the challenge from the signature.
        let challenge = self.signature.challenge();
        // Retrieve the response from the signature.
        let response = self.signature.response();

        if let Err(error) = self.input_ids.iter().zip_eq(&self.inputs).try_for_each(|(input_id, input)| {
            match input_id {
                // A constant input is hashed to a field element.
                InputID::Constant(input_hash) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, StackValue::Plaintext(..)), "Expected a plaintext input");
                    // Hash the input to a field element.
                    let candidate_input_hash = N::hash_bhp1024(&input.to_bits_le())?;
                    // Ensure the input hash matches.
                    ensure!(*input_hash == candidate_input_hash, "Expected a constant input with the same hash");
                }
                // A public input is hashed to a field element.
                InputID::Public(input_hash) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, StackValue::Plaintext(..)), "Expected a plaintext input");
                    // Hash the input to a field element.
                    let candidate_input_hash = N::hash_bhp1024(&input.to_bits_le())?;
                    // Ensure the input hash matches.
                    ensure!(*input_hash == candidate_input_hash, "Expected a public input with the same hash");
                }
                // A private input is encrypted (using `tvk`) and hashed to a field element.
                InputID::Private(index, input_hash) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, StackValue::Plaintext(..)), "Expected a plaintext input");
                    // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = N::hash_to_scalar_psd2(&[self.tvk, *index])?;
                    // Compute the ciphertext.
                    let ciphertext = match &input {
                        StackValue::Plaintext(plaintext) => plaintext.encrypt(&self.caller, randomizer)?,
                        // Ensure the input is a plaintext.
                        StackValue::Record(..) => bail!("Expected a plaintext input, found a record input"),
                    };
                    // Hash the ciphertext to a field element.
                    let candidate_input_hash = N::hash_bhp1024(&ciphertext.to_bits_le())?;
                    // Ensure the input hash matches.
                    ensure!(*input_hash == candidate_input_hash, "Expected a private input with the same commitment");
                }
                // An input record is computed to its serial number.
                InputID::Record(commitment, h, h_r, gamma, serial_number) => {
                    // Compute the record commitment.
                    let candidate_commitment = match &input {
                        StackValue::Record(record) => record.to_commitment()?,
                        // Ensure the input is a record.
                        StackValue::Plaintext(..) => bail!("Expected a record input, found a plaintext input"),
                    };
                    // Ensure the commitment matches.
                    ensure!(*commitment == candidate_commitment, "Expected a record input with the same commitment");

                    // Compute the generator `H` as `HashToGroup(commitment)`.
                    let candidate_h = N::hash_to_group_psd2(&[N::serial_number_domain(), *commitment])?;
                    // Ensure the generator H matches.
                    ensure!(*h == candidate_h, "Expected a record input with the same generator H");

                    // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
                    let candidate_h_r = (*gamma * challenge) + (*h * response);
                    // Ensure the generator `h_r` matches.
                    ensure!(*h_r == candidate_h_r, "Expected a record input with the same generator h_r");

                    // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
                    let sn_nonce = N::hash_to_scalar_psd2(&[
                        N::serial_number_domain(),
                        gamma.mul_by_cofactor().to_x_coordinate(),
                    ])?;
                    // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
                    let candidate_sn =
                        N::commit_bhp512(&(N::serial_number_domain(), *commitment).to_bits_le(), &sn_nonce)?;
                    // Ensure the serial number matches.
                    ensure!(*serial_number == candidate_sn, "Expected a record input with the same serial number");
                }
            }
            Ok(())
        }) {
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
    use crate::{Plaintext, Record};
    use snarkvm_console_account::PrivateKey;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(crate) const ITERATIONS: usize = 1000;

    #[test]
    fn test_sign_and_verify() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Sample a random private key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
            let caller = Address::try_from(&private_key)?;

            // Retrieve `sk_sig` and `pr_sig`.
            let sk_sig = private_key.sk_sig();
            let pr_sig = ComputeKey::try_from(&private_key)?.pr_sig();

            // Construct a program ID and function name.
            let program_id = ProgramID::from_str("token.aleo")?;
            let function_name = Identifier::from_str("transfer")?;

            // Construct four inputs.
            let input_constant =
                StackValue::Plaintext(Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap());
            let input_public = StackValue::Plaintext(Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap());
            let input_private = StackValue::Plaintext(Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap());
            let input_record = StackValue::Record(Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap());
            let inputs = vec![input_constant, input_public, input_private, input_record];

            // Construct the input types.
            let input_types = vec![
                ValueType::from_str("amount.constant").unwrap(),
                ValueType::from_str("amount.public").unwrap(),
                ValueType::from_str("amount.private").unwrap(),
                ValueType::from_str("token.record").unwrap(),
            ];

            // Compute the signed request.
            let request = Request::sign(&sk_sig, &pr_sig, program_id, function_name, inputs, &input_types, rng)?;
            assert!(request.verify());
        }
        Ok(())
    }
}
