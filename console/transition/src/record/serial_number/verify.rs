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

impl<N: Network> SerialNumber<N> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_number == serial_number') where:
    ///     challenge' := HashToScalar(H, r * H, gamma, r * G, pk_sig, pr_sig, address, message)
    pub fn verify(&self, address: &Address<N>, message: &[Field<N>], commitment: Field<N>) -> bool {
        // Retrieve the signature components.
        let (challenge, response, compute_key, gamma) = self.signature;
        // Retrieve pk_sig.
        let pk_sig = compute_key.pk_sig();
        // Retrieve pr_sig.
        let pr_sig = compute_key.pr_sig();

        // Compute the generator `H` as `HashToGroup(commitment)`.
        let h = match N::hash_to_group_psd2(&[N::serial_number_domain(), commitment]) {
            Ok(h) => h,
            Err(error) => {
                eprintln!("Failed to compute the generator H: {error}");
                return false;
            }
        };

        // Compute `g_r` as `(challenge * pk_sig) + (response * G)`, equivalent to `r * G`.
        let g_r = (pk_sig * challenge) + N::g_scalar_multiply(&response);

        // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
        let h_r = (gamma * challenge) + (h * response);

        // Construct the hash input as `(H, r * H, gamma, r * G, pk_sig, pr_sig, address, message)`.
        let mut preimage = Vec::with_capacity(8 + message.len());
        preimage.push(N::serial_number_domain());
        preimage.extend([h, h_r, gamma, g_r, pk_sig, pr_sig, **address].map(|point| point.to_x_coordinate()));
        preimage.extend(message);

        // Compute `candidate_challenge` as `HashToScalar(H, r * H, gamma, r * G, pk_sig, pr_sig, address, message)`.
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
            match N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &serial_number_nonce) {
                Ok(candidate_serial_number) => candidate_serial_number,
                Err(error) => {
                    eprintln!("Failed to compute the serial number: {error}");
                    return false;
                }
            };

        // Return `true` if the challenge, address, and serial number are valid.
        challenge == candidate_challenge
            && *address == candidate_address
            && self.serial_number == candidate_serial_number
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
            let message = Uniform::rand(rng);
            let commitment = Uniform::rand(rng);

            let sk_sig = private_key.sk_sig();
            let pr_sig = ComputeKey::try_from(&private_key)?.pr_sig();
            let address = Address::try_from(&private_key)?;

            let serial_number = SerialNumber::<CurrentNetwork>::sign(&sk_sig, &pr_sig, &[message], commitment, rng)?;
            assert!(serial_number.verify(&address, &[message], commitment));
        }
        Ok(())
    }
}
