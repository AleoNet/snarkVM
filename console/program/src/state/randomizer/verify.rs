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
    pub fn verify(&self, address: &Address<N>, serial_numbers: &[N::Field], output_index: u16) -> bool {
        // Retrieve the proof components.
        let (gamma, challenge, response) = self.proof;

        // Construct the input as: [ serial_numbers || output_index ].
        let mut input = Vec::with_capacity(serial_numbers.len() + 1);
        input.extend_from_slice(serial_numbers);
        input.push(N::Field::from(output_index as u128));

        // Hash the input as `Hash(serial_numbers || output_index)`.
        // (For advanced users): The input hash is injected as a public input
        // to the output circuit, which ensures the VRF input is of fixed size.
        let input_hash = match N::hash_psd4(&input) {
            Ok(input_hash) => input_hash,
            Err(err) => {
                eprintln!("Failed to compute the input hash: {err}");
                return false;
            }
        };

        // Compute the generator `H` as `HashToGroup(input_hash)`.
        let generator_h = match N::hash_to_group_psd2(&[N::randomizer_domain(), input_hash]) {
            Ok(generator_h) => generator_h,
            Err(err) => {
                eprintln!("Failed to compute the generator H: {err}");
                return false;
            }
        };

        // Compute `u` as `(challenge * address) + (response * G)`, equivalent to `nonce * G`.
        let u = (((*address).to_projective() * challenge) + N::g_scalar_multiply(&response)).to_affine();

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `nonce * H`.
        let v = ((gamma.to_projective() * challenge) + (generator_h * response)).to_affine();

        // Compute `candidate_challenge` as `HashToScalar(address, gamma, nonce * G, nonce * H)`.
        let candidate_challenge = match N::hash_to_scalar_psd4(&[**address, gamma, u, v].map(|c| c.to_x_coordinate())) {
            Ok(candidate_challenge) => candidate_challenge,
            Err(err) => {
                eprintln!("Failed to compute the challenge: {err}");
                return false;
            }
        };

        // Compute `candidate_randomizer` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_randomizer = match N::hash_to_scalar_psd2(&[gamma.mul_by_cofactor().to_x_coordinate()]) {
            Ok(candidate_randomizer) => candidate_randomizer,
            Err(err) => {
                eprintln!("Failed to compute the randomizer: {err}");
                return false;
            }
        };

        // Return `true` the randomizer is valid.
        challenge == candidate_challenge && self.randomizer == candidate_randomizer
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_account::{Address, PrivateKey, ViewKey};
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::{test_crypto_rng, UniformRand};

    type CurrentNetwork = Testnet3;

    pub(crate) const ITERATIONS: usize = 1000;

    #[test]
    fn test_prove_and_verify() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
            let view_key = ViewKey::<CurrentNetwork>::try_from(&private_key)?;
            let address = Address::<CurrentNetwork>::try_from(&view_key)?;

            let serial_numbers = (0..rng.gen_range(0..255)).map(|_| UniformRand::rand(rng)).collect::<Vec<_>>();
            let output_index = UniformRand::rand(rng);

            let randomizer = Randomizer::<CurrentNetwork>::prove(&view_key, &serial_numbers, output_index, rng)?;
            assert!(randomizer.verify(&address, &serial_numbers, output_index));
        }
        Ok(())
    }
}
