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

        // Compute the generator `H` as `HashToCurve(commitment)`.
        let generator_h = match N::hash_to_group_psd2(&[commitment]) {
            Ok(generator_h) => generator_h,
            Err(err) => {
                eprintln!("Failed to compute the generator H: {}", err);
                return false;
            }
        };

        // Compute `u` as `(challenge * pk_vrf) + (response * G)`, equivalent to `randomizer * G`.
        let u = ((pk_vrf.to_projective() * challenge) + N::g_scalar_multiply(&response)).to_affine();

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `randomizer * H`.
        let v = ((gamma.to_projective() * challenge) + (generator_h * response)).to_affine();

        // Compute `candidate_challenge` as `HashToScalar(pk_vrf, gamma, randomizer * G, randomizer * H)`.
        let candidate_challenge = match N::hash_to_scalar_psd4(&[pk_vrf, &gamma, &u, &v].map(|c| c.to_x_coordinate())) {
            Ok(candidate_challenge) => candidate_challenge,
            Err(err) => {
                eprintln!("Failed to compute the challenge: {}", err);
                return false;
            }
        };

        // Compute `candidate_output` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_output = match N::hash_to_scalar_psd4(&[gamma.mul_by_cofactor().to_x_coordinate()]) {
            Ok(candidate_output) => candidate_output,
            Err(err) => {
                eprintln!("Failed to compute the output: {}", err);
                return false;
            }
        };

        // Return whether the proof is valid.
        challenge == candidate_challenge && self.output == candidate_output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::{test_rng, UniformRand};

    type CurrentNetwork = Testnet3;

    pub(crate) const ITERATIONS: usize = 10000;

    #[test]
    fn test_prove_and_verify() -> Result<()> {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            let sk_vrf = UniformRand::rand(rng);
            let commitment = UniformRand::rand(rng);
            let randomizer = UniformRand::rand(rng);

            let pk_vrf = CurrentNetwork::g_scalar_multiply(&sk_vrf).to_affine();

            let proof = SerialNumber::<CurrentNetwork>::prove(&sk_vrf, commitment, randomizer)?;
            assert!(proof.verify(&pk_vrf, commitment));
        }
        Ok(())
    }
}
