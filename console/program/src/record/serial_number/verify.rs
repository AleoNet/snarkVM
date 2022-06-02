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
    /// Returns `true` if the proof is valid, and `false` otherwise.
    pub fn verify(&self, pk_vrf: &N::Affine, commitment: N::Field) -> bool {
        // Retrieve the proof components.
        let (gamma, challenge, response) = self.proof;

        // Compute the generator `H` as `HashToGroup(commitment)`.
        let generator_h = match N::hash_to_group_psd2(&[N::serial_number_domain(), commitment]) {
            Ok(generator_h) => generator_h,
            Err(error) => {
                eprintln!("Failed to compute the generator H: {error}");
                return false;
            }
        };

        // Compute `u` as `(challenge * pk_vrf) + (response * G)`, equivalent to `nonce * G`.
        let u = ((pk_vrf.to_projective() * challenge) + N::g_scalar_multiply(&response)).to_affine();

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `nonce * H`.
        let v = ((gamma.to_projective() * challenge) + (generator_h * response)).to_affine();

        // Compute `candidate_challenge` as `HashToScalar(pk_vrf, gamma, nonce * G, nonce * H)`.
        let candidate_challenge = match N::hash_to_scalar_psd4(&[pk_vrf, &gamma, &u, &v].map(|c| c.to_x_coordinate())) {
            Ok(candidate_challenge) => candidate_challenge,
            Err(error) => {
                eprintln!("Failed to compute the challenge: {error}");
                return false;
            }
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

        // Return `true` the challenge and serial number is valid.
        challenge == candidate_challenge && self.serial_number == candidate_serial_number
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_account::Address;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::{test_crypto_rng, UniformRand};

    type CurrentNetwork = Testnet3;

    pub(crate) const ITERATIONS: usize = 1000;

    #[test]
    fn test_prove_and_verify() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            let sk_vrf = UniformRand::rand(rng);
            let commitment = UniformRand::rand(rng);

            let pk_vrf = CurrentNetwork::g_scalar_multiply(&sk_vrf).to_affine();

            let serial_number = SerialNumber::<CurrentNetwork>::prove(&sk_vrf, commitment, rng)?;
            assert!(serial_number.verify(&pk_vrf, commitment));
        }
        Ok(())
    }
}
