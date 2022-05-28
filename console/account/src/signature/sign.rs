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

impl<N: Network> Signature<N> {
    /// Returns a signature `(challenge, response, compute_key)` for a given message and randomizer, where:
    ///     challenge := HashToScalar(address, G^randomizer, message)
    ///     response := randomizer - challenge * private_key.sk_sig()
    pub fn sign(private_key: &PrivateKey<N>, message: &[bool], randomizer: N::Scalar) -> Result<Self> {
        // Compute G^randomizer.
        let g_randomizer = N::g_scalar_multiply(&randomizer).to_affine();

        // Derive the compute key from the private key.
        let compute_key = ComputeKey::try_from(private_key)?;
        // Derive the address from the compute key.
        let address = Address::try_from(compute_key)?;

        // TODO(howardwu): Abstraction - Abstract this logic into a dedicated function.
        // Convert the message into field elements.
        let message_elements = message
            .chunks(N::Field::size_in_data_bits())
            .map(|data_bits| N::field_from_bits_le(data_bits))
            .collect::<Result<Vec<_>>>()?;

        // Construct the hash input (address, G^randomizer, message).
        let mut preimage = Vec::with_capacity(3 + message_elements.len());
        preimage.push(address.to_x_coordinate());
        preimage.push(g_randomizer.to_x_coordinate());
        preimage.push(N::Field::from(message.len() as u128));
        preimage.extend_from_slice(&message_elements);

        // Compute the verifier challenge.
        let challenge = N::hash_to_scalar_psd8(&preimage)?;

        // Compute the prover response.
        let response = randomizer - (challenge * private_key.sk_sig());

        // Output the signature.
        Ok(Self { challenge, response, compute_key })
    }

    ///
    /// Verifies (challenge == challenge') && (address == address') where:
    ///     challenge' := HashToScalar(address', G^response pk_sig^challenge, message)
    ///
    pub fn verify(&self, address: &Address<N>, message: &[bool]) -> bool {
        // Derive the compute key from the address, and return `false` if this operation fails.
        let candidate_address = match Address::try_from(self.compute_key) {
            // Output the computed candidate address.
            Ok(candidate_address) => candidate_address,
            // Return `false` if the address is invalid.
            Err(_) => return false,
        };

        // Compute pk_sig_challenge := pk_sig^challenge.
        let pk_sig_challenge = self.compute_key.pk_sig().to_projective() * self.challenge;

        // Compute G^randomizer := G^response pk_sig_challenge.
        let g_randomizer = (N::g_scalar_multiply(&self.response) + pk_sig_challenge).to_affine();

        // TODO(howardwu): Abstraction - Abstract this logic into a dedicated function.
        // Convert the message into field elements.
        let message_elements = match message
            .chunks(N::Field::size_in_data_bits())
            .map(|data_bits| N::field_from_bits_le(data_bits))
            .collect::<Result<Vec<_>>>()
        {
            // Output the computed message elements.
            Ok(message_elements) => message_elements,
            // Return `false` if the message is invalid.
            Err(_) => return false,
        };

        // Construct the hash input (address, G^randomizer, message).
        let mut preimage = Vec::with_capacity(3 + message_elements.len());
        preimage.push(address.to_x_coordinate());
        preimage.push(g_randomizer.to_x_coordinate());
        preimage.push(N::Field::from(message.len() as u128));
        preimage.extend_from_slice(&message_elements);

        // Hash to derive the verifier challenge, and return `false` if this operation fails.
        let candidate_challenge = match N::hash_to_scalar_psd8(&preimage) {
            // Output the computed candidate challenge.
            Ok(candidate_challenge) => candidate_challenge,
            // Return `false` if the address is invalid.
            Err(_) => return false,
        };

        // Return `true` if the candidate challenge and address are correct.
        self.challenge == candidate_challenge && *address == candidate_address
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::{test_crypto_rng, test_rng, UniformRand};

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    fn check_sign_and_verify(message: &[bool]) -> Result<()> {
        // Sample an address and a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
        let address = Address::try_from(&private_key)?;

        // Generate a signature.
        let randomizer = UniformRand::rand(&mut test_crypto_rng());
        let signature = Signature::sign(&private_key, message, randomizer)?;
        assert!(signature.verify(&address, message));
        Ok(())
    }

    fn check_sign_and_verify_fails(message: &[bool], bad_message: &[bool]) -> Result<()> {
        // Sample an address and a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
        let address = Address::try_from(&private_key)?;

        // Generate a signature.
        let randomizer = UniformRand::rand(&mut test_crypto_rng());
        let signature = Signature::sign(&private_key, message, randomizer)?;
        assert!(!signature.verify(&address, bad_message));
        Ok(())
    }

    #[test]
    fn test_sign_and_verify() -> Result<()> {
        for i in 0..ITERATIONS {
            // Check that the signature is valid for the message.
            let message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
            check_sign_and_verify(&message)?;

            // Check that the signature is invalid for an incorrect message.
            let failure_message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
            if message != failure_message {
                check_sign_and_verify_fails(&message, &failure_message)?;
            }
        }
        Ok(())
    }
}
