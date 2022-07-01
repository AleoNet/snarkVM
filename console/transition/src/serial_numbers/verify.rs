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

impl<N: Network> SerialNumbers<N> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_numbers == serial_numbers') where:
    ///     challenge' := HashToScalar(r * G, pk_sig, pr_sig, address, function_call, ∀ \[H, r * H, gamma\])
    pub fn verify(&self, address: &Address<N>, function_call: &[Field<N>], commitments: &[Field<N>]) -> bool {
        // Retrieve the signature components.
        let (challenge, response, compute_key, gammas) = &self.signature;

        // Retrieve pk_sig.
        let pk_sig = compute_key.pk_sig();
        // Retrieve pr_sig.
        let pr_sig = compute_key.pr_sig();
        // Compute `g_r` as `(challenge * pk_sig) + (response * G)`, equivalent to `r * G`.
        let g_r = (pk_sig * challenge) + N::g_scalar_multiply(response);

        // Construct the hash input as `(r * G, pk_sig, pr_sig, address, function_call, ∀ [H, r * H, gamma])`.
        let mut preimage = Vec::with_capacity(4 + (3 * commitments.len()) + function_call.len());
        preimage.push(N::serial_number_domain());
        preimage.extend([g_r, pk_sig, pr_sig, **address].map(|point| point.to_x_coordinate()));
        preimage.extend(function_call);

        for ((gamma, commitment), serial_number) in gammas.into_iter().zip_eq(commitments).zip_eq(&self.serial_numbers)
        {
            // Compute the generator `H` as `HashToGroup(commitment)`.
            let h = match N::hash_to_group_psd2(&[N::serial_number_domain(), *commitment]) {
                Ok(h) => h,
                Err(error) => {
                    eprintln!("Failed to compute the generator H: {error}");
                    return false;
                }
            };

            // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
            let h_r = (*gamma * challenge) + (h * response);

            // Compute `serial_number_nonce` as `HashToScalar(COFACTOR * gamma)`.
            let serial_number_nonce =
                match N::hash_to_scalar_psd2(&[N::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]) {
                    Ok(serial_number_nonce) => serial_number_nonce,
                    Err(error) => {
                        eprintln!("Failed to compute the serial number nonce: {error}");
                        return false;
                    }
                };

            // Compute `candidate_serial_number` as `Commit(commitment, serial_number_nonce)`.
            let candidate_serial_number =
                match N::commit_bhp512(&(N::serial_number_domain(), *commitment).to_bits_le(), &serial_number_nonce) {
                    Ok(candidate_serial_number) => candidate_serial_number,
                    Err(error) => {
                        eprintln!("Failed to compute the serial number: {error}");
                        return false;
                    }
                };

            // Append `(H, r * H, gamma)` to the hash input.
            preimage.extend([h, h_r, *gamma].iter().map(|point| point.to_x_coordinate()));

            // Ensure the computed serial number match the expected serial number.
            if *serial_number != candidate_serial_number {
                eprintln!("Failed to verify the serial number: {serial_number} != {candidate_serial_number}");
                return false;
            }
        }

        // Compute `candidate_challenge` as `HashToScalar(r * G, pk_sig, pr_sig, address, function_call, ∀ [H, r * H, gamma])`.
        let candidate_challenge = match N::hash_to_scalar_psd8(&preimage) {
            Ok(candidate_challenge) => candidate_challenge,
            Err(error) => {
                eprintln!("Failed to compute the challenge: {error}");
                return false;
            }
        };

        // Derive the address from the compute key, and return `false` if this operation fails.
        let candidate_address = match Address::try_from(compute_key) {
            // Output the computed candidate address.
            Ok(candidate_address) => candidate_address,
            // Return `false` if the address errored.
            Err(_) => return false,
        };

        // Return `true` if the challenge and address are valid.
        *challenge == candidate_challenge && *address == candidate_address
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
    fn test_sign_and_verify() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
            let commitments = vec![Uniform::rand(rng), Uniform::rand(rng)];

            let sk_sig = private_key.sk_sig();
            let pr_sig = ComputeKey::try_from(&private_key)?.pr_sig();
            let address = Address::try_from(&private_key)?;

            let serial_numbers =
                SerialNumbers::<CurrentNetwork>::sign(&sk_sig, &pr_sig, &commitments, &commitments, rng)?;
            assert!(serial_numbers.verify(&address, &commitments, &commitments));
        }
        Ok(())
    }
}
