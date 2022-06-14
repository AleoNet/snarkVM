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

impl<N: Network> Randomizer<N> {
    /// Returns `true` if the proof is valid, and `false` otherwise.
    pub fn verify(&self, address: &Address<N>, serial_numbers_digest: Field<N>, output_index: U16<N>) -> bool {
        // Retrieve the proof components.
        let (gamma, challenge, response) = self.proof;

        // Compute the generator `H` as `HashToGroup([ Hash(serial_numbers) || output_index ])`.
        let generator_h = match N::hash_to_group_psd4(&[
            N::randomizer_domain(),
            serial_numbers_digest,
            Field::from_u16(*output_index),
        ]) {
            Ok(generator_h) => generator_h,
            Err(err) => {
                eprintln!("Failed to compute the generator H: {err}");
                return false;
            }
        };

        // Compute `u` as `(challenge * address) + (response * G)`, equivalent to `nonce * G`.
        let u = (**address * challenge) + N::g_scalar_multiply(&response);

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `nonce * H`.
        let v = (gamma * challenge) + (generator_h * response);

        // Compute `candidate_challenge` as `HashToScalar(address, gamma, nonce * G, nonce * H)`.
        let candidate_challenge = match N::hash_to_scalar_psd4(&[**address, gamma, u, v].map(|c| c.to_x_coordinate())) {
            Ok(candidate_challenge) => candidate_challenge,
            Err(err) => {
                eprintln!("Failed to compute the challenge: {err}");
                return false;
            }
        };

        // Compute `candidate_randomizer` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_randomizer =
            match N::hash_to_scalar_psd2(&[N::randomizer_domain(), gamma.mul_by_cofactor().to_x_coordinate()]) {
                Ok(candidate_randomizer) => candidate_randomizer,
                Err(err) => {
                    eprintln!("Failed to compute the randomizer: {err}");
                    return false;
                }
            };

        // Return `true` the challenge and randomizer is valid.
        challenge == candidate_challenge && self.randomizer == candidate_randomizer
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_account::{Address, PrivateKey, ViewKey};
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(crate) const ITERATIONS: usize = 1000;

    #[test]
    fn test_prove_and_verify() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
            let view_key = ViewKey::<CurrentNetwork>::try_from(&private_key)?;
            let address = Address::<CurrentNetwork>::try_from(&view_key)?;

            let serial_numbers = (0..rng.gen_range(0..255)).map(|_| Uniform::rand(rng)).collect::<Vec<_>>();
            let output_index = Uniform::rand(rng);

            let randomizer = Randomizer::<CurrentNetwork>::prove(&view_key, &serial_numbers, output_index, rng)?;

            // Hash the input as `Hash(serial_numbers)`.
            let serial_numbers_digest = <CurrentNetwork as Network>::hash_bhp1024(&serial_numbers.to_bits_le())?;

            assert!(randomizer.verify(&address, serial_numbers_digest, output_index));
        }
        Ok(())
    }
}
