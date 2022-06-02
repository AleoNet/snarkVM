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
    /// Returns a new serial number and proof, given a VRF secret key, commitment, and an RNG.
    pub fn prove<R: Rng + CryptoRng>(sk_vrf: &N::Scalar, commitment: N::Field, rng: &mut R) -> Result<Self> {
        // Sample a random nonce from the scalar field.
        let nonce = N::Scalar::rand(rng);

        // Compute the generator `H` as `HashToGroup(commitment)`.
        let generator_h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;

        // Compute `pk_vrf` as `sk_vrf * G`.
        let pk_vrf = N::g_scalar_multiply(sk_vrf);
        // Compute `gamma` as `sk_vrf * H`.
        let gamma = generator_h * *sk_vrf;
        // Compute `u` as `nonce * G`.
        let u = N::g_scalar_multiply(&nonce);
        // Compute `v` as `nonce * H`.
        let v = generator_h * nonce;

        // Prepare the preimage as `(pk_vrf, gamma, u, v)`, and use the x-coordinate of each affine point.
        let mut preimage = [pk_vrf, gamma, u, v];
        N::Projective::batch_normalization(&mut preimage);
        let [pk_vrf, gamma, u, v] = preimage.map(|c| c.to_affine());

        // Compute `challenge` as `HashToScalar(sk_vrf * G, gamma, nonce * G, nonce * H)`.
        let challenge = N::hash_to_scalar_psd4(&[pk_vrf, gamma, u, v].map(|c| c.to_x_coordinate()))?;
        // Compute `response` as `nonce - challenge * sk_vrf`.
        let response = nonce - challenge * sk_vrf;

        // Compute `serial_number_nonce` as `Hash(COFACTOR * gamma)`.
        let serial_number_nonce =
            N::hash_to_scalar_psd2(&[N::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()])?;

        // Compute `serial_number` as `Commit(commitment, serial_number_nonce)`.
        let serial_number =
            N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &serial_number_nonce)?;

        // Return the serial number and proof.
        Ok(Self { serial_number, proof: (gamma, challenge, response) })
    }
}
