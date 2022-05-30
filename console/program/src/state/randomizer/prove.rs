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
    /// Returns a new randomizer and proof, given a view key, input, and RNG.
    pub fn prove<R: Rng + CryptoRng>(
        view_key: &ViewKey<N>,
        commitments: &[N::Field],
        output_index: u16,
        rng: &mut R,
    ) -> Result<Self> {
        // Sample a random nonce from the scalar field.
        let nonce = N::Scalar::rand(rng);

        // Construct the input as: [ commitments || output_index ].
        let mut input = Vec::with_capacity(commitments.len() + 1);
        input.extend_from_slice(commitments);
        input.push(N::Field::from(output_index as u128));

        // Hash the input as `Hash(commitments || output_index)`.
        // (For advanced users): The input hash is injected as a public input
        // to the output circuit, which ensures the VRF input is of fixed size.
        let input_hash = N::hash_psd4(&input)?;

        // Compute the generator `H` as `HashToGroup(input_hash)`.
        let generator_h = N::hash_to_group_psd2(&[input_hash])?;

        // Compute `address` as `view_key * G`.
        let address = Address::try_from(view_key)?;
        // Compute `gamma` as `view_key * H`.
        let gamma = generator_h * **view_key;
        // Compute `u` as `nonce * G`.
        let u = N::g_scalar_multiply(&nonce);
        // Compute `v` as `nonce * H`.
        let v = generator_h * nonce;

        // Convert `(gamma, u, v)` into affine form.
        let mut preimage = [gamma, u, v];
        N::Projective::batch_normalization(&mut preimage);
        let [gamma, u, v] = preimage.map(|c| c.to_affine());

        // Compute `challenge` as `HashToScalar(address, gamma, nonce * G, nonce * H)`.
        let challenge = N::hash_to_scalar_psd4(&[*address, gamma, u, v].map(|c| c.to_x_coordinate()))?;
        // Compute `response` as `nonce - challenge * view_key`.
        let response = nonce - challenge * **view_key;

        // Compute `randomizer` as `HashToScalar(COFACTOR * gamma)`.
        let randomizer = N::hash_to_scalar_psd4(&[gamma.mul_by_cofactor().to_x_coordinate()])?;

        // Return the proof.
        Ok(Self { randomizer, proof: (gamma, challenge, response) })
    }
}
