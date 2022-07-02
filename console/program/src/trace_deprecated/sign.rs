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

impl<N: Network> Call<N> {
    /// Returns the request, serial numbers, and signature `(challenge, response, compute_key, gammas)` for a given call and RNG, where:
    ///     challenge := HashToScalar(r * G, pk_sig, pr_sig, address, request, ∀ \[H, r * H, gamma\])
    ///     response := r - challenge * sk_sig
    pub fn sign<R: Rng + CryptoRng>(
        sk_sig: &Scalar<N>,
        pr_sig: &Group<N>,
        request: &Request<N>,
        commitments: &[Field<N>],
        rng: &mut R,
    ) -> Result<Self> {
        // Sample a random nonce.
        let nonce = Field::<N>::rand(rng);
        // Compute a `r` as `HashToScalar(sk_sig || nonce || Hash(function_call))`.
        let r = N::hash_to_scalar_psd2(&[sk_sig.to_field()?, nonce, N::hash_psd8(function_call)?])?;

        // Compute `g_r` as `r * G`.
        let g_r = N::g_scalar_multiply(&r);
        // Compute `pk_sig` as `sk_sig * G`.
        let pk_sig = N::g_scalar_multiply(sk_sig);
        // Derive the compute key.
        let compute_key = ComputeKey::try_from((pk_sig, *pr_sig))?;
        // Derive the address from the compute key.
        let address = Address::try_from(compute_key)?;
        // Ensure the address matches the request caller.
        ensure!(address == request.caller(), "Request caller does not match derived address during signing");

        // Construct the hash input as `(r * G, pk_sig, pr_sig, address, function_call, ∀ [H, r * H, gamma])`.
        let mut preimage = Vec::with_capacity(4 + (3 * commitments.len()) + function_call.len());
        preimage.push(N::serial_number_domain());
        preimage.extend([g_r, pk_sig, *pr_sig, *address].map(|point| point.to_x_coordinate()));
        preimage.extend(function_call);

        // Initialize a vector to store the gammas.
        let mut gammas = Vec::with_capacity(commitments.len());
        // Initialize a vector to store the serial numbers.
        let mut serial_numbers = Vec::with_capacity(commitments.len());

        for commitment in commitments {
            // Compute the generator `H` as `HashToGroup(commitment)`.
            let h = N::hash_to_group_psd2(&[N::serial_number_domain(), *commitment])?;
            // Compute `h_r` as `r * H`.
            let h_r = h * r;
            // Compute `gamma` as `sk_sig * H`.
            let gamma = h * sk_sig;

            // Compute `serial_number_nonce` as `Hash(COFACTOR * gamma)`.
            let serial_number_nonce =
                N::hash_to_scalar_psd2(&[N::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()])?;

            // Compute `serial_number` as `Commit(commitment, serial_number_nonce)`.
            let serial_number =
                N::commit_bhp512(&(N::serial_number_domain(), *commitment).to_bits_le(), &serial_number_nonce)?;

            // Append `(H, r * H, gamma)` to the hash input.
            preimage.extend([h, h_r, gamma].iter().map(|point| point.to_x_coordinate()));
            // Append `gamma` to the vector of gammas.
            gammas.push(gamma);
            // Append the `serial_number` to the serial numbers.
            serial_numbers.push(serial_number);
        }

        // Compute `challenge` as `HashToScalar(r * G, pk_sig, pr_sig, address, function_call, ∀ [H, r * H, gamma])`.
        let challenge = N::hash_to_scalar_psd8(&preimage)?;
        // Compute `response` as `r - challenge * sk_sig`.
        let response = r - challenge * sk_sig;

        // Return the serial numbers and signature.
        Ok(Self { serial_numbers, signature: (challenge, response, compute_key, gammas) })
    }
}
