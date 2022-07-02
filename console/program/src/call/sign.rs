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
    /// Returns the call for a given request, list of input types, private key, and RNG, where:
    ///     challenge := HashToScalar(r * G, pk_sig, pr_sig, caller, \[tvk, input IDs\])
    ///     response := r - challenge * sk_sig
    pub fn sign<R: Rng + CryptoRng>(
        request: &Request<N>,
        input_types: &[ValueType<N>],
        sk_sig: &Scalar<N>,
        pr_sig: &Group<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Sample a random nonce.
        let nonce = Field::<N>::rand(rng);
        // Compute a `r` as `HashToScalar(sk_sig || nonce)`.
        let r = N::hash_to_scalar_psd4(&[N::serial_number_domain(), sk_sig.to_field()?, nonce])?;
        // Compute `g_r` as `r * G`. Note: This is the transition public key `tpk`.
        let g_r = N::g_scalar_multiply(&r);

        // Compute `pk_sig` as `sk_sig * G`.
        let pk_sig = N::g_scalar_multiply(sk_sig);
        // Derive the compute key.
        let compute_key = ComputeKey::try_from((pk_sig, *pr_sig))?;
        // Derive the address from the compute key.
        let caller = Address::try_from(compute_key)?;
        // Ensure the signer matches the request caller.
        ensure!(caller == *request.caller(), "Signer is not the caller of the request");

        // Compute the transition view key `tvk` as `r * caller`.
        let tvk = (*caller * r).to_x_coordinate();

        // Construct the hash input as `(r * G, pk_sig, pr_sig, caller, [tvk, input IDs])`.
        let mut preimage = Vec::with_capacity(5 + 2 * request.inputs().len());
        preimage.extend([g_r, pk_sig, *pr_sig, *caller].map(|point| point.to_x_coordinate()));
        preimage.push(tvk);

        // Initialize a vector to store the input IDs.
        let mut inputs = Vec::with_capacity(request.inputs().len());

        // Prepare the inputs.
        for (index, (input, input_type)) in request.inputs().iter().zip_eq(input_types).enumerate() {
            match input_type {
                // A constant input is hashed to a field element.
                ValueType::Constant(..) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, StackValue::Plaintext(..)), "Expected a plaintext input");
                    // Hash the input to a field element.
                    let input_hash = N::hash_bhp1024(&input.to_bits_le())?;
                    // Add the input ID to the inputs.
                    inputs.push(InputID::Constant(input_hash));
                }
                // A public input is hashed to a field element.
                ValueType::Public(..) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, StackValue::Plaintext(..)), "Expected a plaintext input");
                    // Hash the input to a field element.
                    let input_hash = N::hash_bhp1024(&input.to_bits_le())?;
                    // Add the input ID to the inputs.
                    inputs.push(InputID::Public(input_hash));
                }
                // A private input is committed (using `tvk`) to a field element.
                ValueType::Private(..) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, StackValue::Plaintext(..)), "Expected a plaintext input");
                    // Construct the (console) input index as a field element.
                    let index = Field::from_u16(index as u16);
                    // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = N::hash_to_scalar_psd2(&[tvk, index])?;
                    // Commit the input to a field element.
                    let input_commitment = N::commit_bhp1024(&input.to_bits_le(), &randomizer)?;
                    // Add the input commitment to the inputs.
                    inputs.push(InputID::Private(input_commitment));
                }
                // An input record is computed to its serial number.
                ValueType::Record(..) => {
                    // Compute the record commitment.
                    let commitment = match &input {
                        StackValue::Record(record) => record.to_commitment()?,
                        // Ensure the input is a record.
                        StackValue::Plaintext(..) => bail!("Expected a record input, found a plaintext input"),
                    };

                    // Compute the generator `H` as `HashToGroup(commitment)`.
                    let h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;
                    // Compute `h_r` as `r * H`.
                    let h_r = h * r;
                    // Compute `gamma` as `sk_sig * H`.
                    let gamma = h * sk_sig;

                    // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
                    let sn_nonce = N::hash_to_scalar_psd2(&[
                        N::serial_number_domain(),
                        gamma.mul_by_cofactor().to_x_coordinate(),
                    ])?;
                    // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
                    let serial_number =
                        N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)?;

                    // Add the commitment, H, r * H, gamma, and serial number to the inputs.
                    inputs.push(InputID::Record(commitment, h, h_r, gamma, serial_number));
                }
            }
        }
        // Append the input IDs to the preimage.
        preimage
            .extend(inputs.iter().map(|input| input.to_fields()).collect::<Result<Vec<_>>>()?.into_iter().flatten());

        // Compute `challenge` as `HashToScalar(r * G, pk_sig, pr_sig, caller, [tvk, input IDs])`.
        let challenge = N::hash_to_scalar_psd8(&preimage)?;
        // Compute `response` as `r - challenge * sk_sig`.
        let response = r - challenge * sk_sig;

        Ok(Self {
            caller,
            program_id: *request.program_id(),
            function_name: *request.function_name(),
            input_ids: inputs,
            signature: Signature::from((challenge, response, compute_key)),
            tvk,
        })
    }
}
