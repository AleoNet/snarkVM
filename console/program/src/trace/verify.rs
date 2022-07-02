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

impl<N: Network> Trace<N> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_numbers == serial_numbers') where:
    ///     challenge' := HashToScalar(r * G, pk_sig, pr_sig, caller, \[tvk, input IDs\])
    pub fn verify(&self) -> bool {
        // Construct the input IDs as field elements.
        let input_ids = match self.inputs.iter().map(|input| input.to_fields()).collect::<Result<Vec<_>>>() {
            Ok(input_ids) => input_ids,
            Err(error) => {
                eprintln!("Failed to construct the input IDs: {error}");
                return false;
            }
        };

        // Construct the signature message as `[tvk, input IDs]`.
        let mut message = Vec::with_capacity(1 + input_ids.len());
        message.push(self.tvk);
        message.extend(input_ids.into_iter().flatten());

        // Retrieve the challenge from the signature.
        let challenge = self.signature.challenge();
        // Retrieve the response from the signature.
        let response = self.signature.response();

        // Verify each serial number is computed correctly.
        for input in self.inputs.iter() {
            match input {
                InputID::Constant(..) | InputID::Public(..) | InputID::Private(..) => continue,
                InputID::Record(commitment, h, h_r, gamma, serial_number) => {
                    // Compute the generator `H` as `HashToGroup(commitment)`.
                    match N::hash_to_group_psd2(&[N::serial_number_domain(), *commitment]) {
                        // Ensure the generator `H` matches.
                        Ok(candidate_h) => {
                            if *h != candidate_h {
                                eprintln!("Mismatching generator H: {h} != {candidate_h}");
                                return false;
                            }
                        }
                        Err(error) => {
                            eprintln!("Failed to compute the generator H: {error}");
                            return false;
                        }
                    };

                    // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
                    let candidate_h_r = (*gamma * challenge) + (*h * response);
                    // Ensure `h_r` matches.
                    if *h_r != candidate_h_r {
                        eprintln!("Mismatching h_r: {h_r} != {candidate_h_r}");
                        return false;
                    }

                    // Compute `sn_nonce` as `HashToScalar(COFACTOR * gamma)`.
                    let sn_nonce = match N::hash_to_scalar_psd2(&[
                        N::serial_number_domain(),
                        gamma.mul_by_cofactor().to_x_coordinate(),
                    ]) {
                        Ok(sn_nonce) => sn_nonce,
                        Err(error) => {
                            eprintln!("Failed to compute the serial number nonce: {error}");
                            return false;
                        }
                    };

                    // Compute `candidate_serial_number` as `Commit(commitment, serial_number_nonce)`.
                    match N::commit_bhp512(&(N::serial_number_domain(), *commitment).to_bits_le(), &sn_nonce) {
                        // Ensure the computed serial number match the expected serial number.
                        Ok(candidate_serial_number) => {
                            if *serial_number != candidate_serial_number {
                                eprintln!(
                                    "Failed to verify the serial number: {serial_number} != {candidate_serial_number}"
                                );
                                return false;
                            }
                        }
                        Err(error) => {
                            eprintln!("Failed to compute the serial number: {error}");
                            return false;
                        }
                    };
                }
            }
        }

        // Verify the signature.
        self.signature.verify(&self.caller, &message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Record;
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

            // Construct a program ID and function name.
            let program_id = ProgramID::from_str("token.aleo")?;
            let function_name = Identifier::from_str("transfer")?;

            // Construct two input records.
            let input_record = Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap();
            let input = StackValue::<CurrentNetwork>::Record(input_record.clone());
            let inputs = vec![input.clone(), input.clone()];

            // Construct the input types.
            let input_types = vec![ValueType::Record(Identifier::from_str("token")?); 2];

            // Construct the request.
            let request = Request::new(caller, program_id, function_name, inputs);

            // Retrieve `sk_sig` and `pr_sig`.
            let sk_sig = private_key.sk_sig();
            let pr_sig = ComputeKey::try_from(&private_key)?.pr_sig();

            // Compute the trace by signing the request.
            let trace = Trace::sign(&request, &input_types, &sk_sig, &pr_sig, rng)?;
            assert!(trace.verify());
        }
        Ok(())
    }
}
