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

impl<N: Network> EncryptionRandomizer<N> {
    /// Returns a new NSEC5 proof, given a VRF secret key, an input, and a randomizer.
    pub fn prove(view_key: &ViewKey<N>, commitments: &[N::Field], output_index: u16, randomizer: N::Scalar) -> Result<Self> {
        // Construct the input as: [ commitments || output_index ].
        let mut input = Vec::with_capacity(commitments.len() + 1);
        input.extend_from_slice(commitments);
        input.push(N::Field::from(output_index as u128));

        // Compute the generator `H` as `HashToCurve(commitments || output_index)`.
        let generator_h = N::hash_to_group_psd4(&input)?;

        // Compute `address` as `view_key * G`.
        let address = Address::try_from(view_key)?;
        // Compute `gamma` as `view_key * H`.
        let gamma = generator_h * **view_key;
        // Compute `u` as `randomizer * G`.
        let u = N::g_scalar_multiply(&randomizer);
        // Compute `v` as `randomizer * H`.
        let v = generator_h * randomizer;

        // Convert `(gamma, u, v)` into affine form.
        let mut preimage = [gamma, u, v];
        N::Projective::batch_normalization(&mut preimage);
        let [gamma, u, v] = preimage.map(|c| c.to_affine());

        // Compute `challenge` as `HashToScalar(address, gamma, randomizer * G, randomizer * H)`.
        let challenge = N::hash_to_scalar_psd4(&[*address, gamma, u, v].map(|c| c.to_x_coordinate()))?;
        // Compute `response` as `randomizer - challenge * view_key`.
        let response = randomizer - challenge * **view_key;

        // Compute `output` as `HashToScalar(COFACTOR * gamma)`.
        let output = N::hash_to_scalar_psd4(&[gamma.mul_by_cofactor().to_x_coordinate()])?;

        // Return the proof.
        Ok(Self { output, proof: (gamma, challenge, response) })
    }
}
