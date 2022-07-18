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

impl<N: Network> Request<N> {
    /// Returns the request for a given private key, program ID, function name, inputs, input types, and RNG, where:
    ///     challenge := HashToScalar(r * G, pk_sig, pr_sig, caller, \[tvk, input IDs\])
    ///     response := r - challenge * sk_sig
    pub fn sign<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        program_id: ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        input_types: &[ValueType<N>],
        rng: &mut R,
    ) -> Result<Self> {
        // Ensure the number of inputs matches the number of input types.
        if input_types.len() != inputs.len() {
            bail!(
                "Function '{}' in the program '{}' expects {} inputs, but {} were provided.",
                function_name,
                program_id,
                input_types.len(),
                inputs.len()
            )
        }

        // Retrieve `sk_sig`.
        let sk_sig = private_key.sk_sig();
        // Derive the compute key.
        let compute_key = ComputeKey::try_from(private_key)?;
        // Retrieve `pk_sig`.
        let pk_sig = compute_key.pk_sig();
        // Retrieve `pr_sig`.
        let pr_sig = compute_key.pr_sig();

        // Sample a random nonce.
        let nonce = Field::<N>::rand(rng);
        // Compute a `r` as `HashToScalar(sk_sig || nonce)`. Note: This is the transition secret key `tsk`.
        let r = N::hash_to_scalar_psd4(&[N::serial_number_domain(), sk_sig.to_field()?, nonce])?;
        // Compute `g_r` as `r * G`. Note: This is the transition public key `tpk`.
        let g_r = N::g_scalar_multiply(&r);

        // Derive the caller from the compute key.
        let caller = Address::try_from(compute_key)?;
        // Compute the transition view key `tvk` as `r * caller`.
        let tvk = (*caller * r).to_x_coordinate();

        // Compute the function ID as `Hash(network_id, program_id, function_name)`.
        let function_id = N::hash_bhp1024(
            &[
                U16::<N>::new(N::ID).to_bits_le(),
                program_id.name().to_bits_le(),
                program_id.network().to_bits_le(),
                function_name.to_bits_le(),
            ]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>(),
        )?;

        // Construct the hash input as `(r * G, pk_sig, pr_sig, caller, [tvk, function ID, input IDs])`.
        let mut preimage = Vec::with_capacity(5 + 2 * inputs.len());
        preimage.extend([g_r, pk_sig, pr_sig, *caller].map(|point| point.to_x_coordinate()));
        preimage.extend([tvk, function_id]);

        // Initialize a vector to store the input IDs.
        let mut input_ids = Vec::with_capacity(inputs.len());

        // Prepare the inputs.
        for (index, (input, input_type)) in inputs.iter().zip_eq(input_types).enumerate() {
            match input_type {
                // A constant input is hashed to a field element.
                ValueType::Constant(..) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                    // Hash the input to a field element.
                    let input_hash = N::hash_bhp1024(&input.to_bits_le())?;
                    // Add the input hash to the preimage.
                    preimage.push(input_hash);
                    // Add the input ID to the inputs.
                    input_ids.push(InputID::Constant(input_hash));
                }
                // A public input is hashed to a field element.
                ValueType::Public(..) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                    // Hash the input to a field element.
                    let input_hash = N::hash_bhp1024(&input.to_bits_le())?;
                    // Add the input hash to the preimage.
                    preimage.push(input_hash);
                    // Add the input ID to the inputs.
                    input_ids.push(InputID::Public(input_hash));
                }
                // A private input is encrypted (using `tvk`) and hashed to a field element.
                ValueType::Private(..) => {
                    // Ensure the input is a plaintext.
                    ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                    // Construct the (console) input index as a field element.
                    let index = Field::from_u16(index as u16);
                    // Compute the input view key as `Hash(tvk || index)`.
                    let input_view_key = N::hash_psd2(&[tvk, index])?;
                    // Compute the ciphertext.
                    let ciphertext = match &input {
                        Value::Plaintext(plaintext) => plaintext.encrypt_symmetric(input_view_key)?,
                        // Ensure the input is a plaintext.
                        Value::Record(..) => bail!("Expected a plaintext input, found a record input"),
                    };
                    // Hash the ciphertext to a field element.
                    let input_hash = N::hash_bhp1024(&ciphertext.to_bits_le())?;
                    // Add the input hash to the preimage.
                    preimage.push(input_hash);
                    // Add the input hash to the inputs.
                    input_ids.push(InputID::Private(input_hash));
                }
                // A record input is computed to its serial number.
                ValueType::Record(record_name) => {
                    // Construct the (console) input index as a field element.
                    let index = Field::from_u16(index as u16);
                    // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                    let randomizer = N::hash_to_scalar_psd2(&[tvk, index])?;
                    // Retrieve the record.
                    let record = match &input {
                        Value::Record(record) => record,
                        // Ensure the input is a record.
                        Value::Plaintext(..) => bail!("Expected a record input, found a plaintext input"),
                    };
                    // Compute the record commitment.
                    let commitment = record.to_commitment(&program_id, record_name, &randomizer)?;
                    // Ensure the record belongs to the caller.
                    ensure!(**record.owner() == caller, "Input record does not belong to the signer");
                    // Ensure the record gates is less than or equal to 2^52.
                    if !(**record.gates()).to_bits_le()[52..].iter().all(|bit| !bit) {
                        bail!("Input record contains an invalid Aleo balance (in gates): {}", record.gates());
                    }

                    // Compute the generator `H` as `HashToGroup(commitment)`.
                    let h = N::hash_to_group_psd2(&[N::serial_number_domain(), commitment])?;
                    // Compute `h_r` as `r * H`.
                    let h_r = h * r;
                    // Compute `gamma` as `sk_sig * H`.
                    let gamma = h * sk_sig;
                    // Add `H`, `r * H`, and `gamma` to the preimage.
                    preimage.extend([h, h_r, gamma].iter().map(|point| point.to_x_coordinate()));

                    // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
                    let sn_nonce = N::hash_to_scalar_psd2(&[
                        N::serial_number_domain(),
                        gamma.mul_by_cofactor().to_x_coordinate(),
                    ])?;
                    // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
                    let serial_number =
                        N::commit_bhp512(&(N::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)?;
                    // Add gamma and the serial number to the inputs.
                    input_ids.push(InputID::Record(gamma, serial_number));
                }
                // An external record input is committed (using `tvk`) to a field element.
                ValueType::ExternalRecord(..) => {
                    // Ensure the input is a record.
                    ensure!(matches!(input, Value::Record(..)), "Expected a record input");
                    // Construct the (console) input index as a field element.
                    let index = Field::from_u16(index as u16);
                    // Compute the input randomizer as `HashToScalar(tvk || index)`.
                    let input_randomizer = N::hash_to_scalar_psd2(&[tvk, index])?;
                    // Commit to the input to a field element.
                    let input_commitment = N::commit_bhp1024(&input.to_bits_le(), &input_randomizer)?;
                    // Add the input commitment to the preimage.
                    preimage.push(input_commitment);
                    // Add the input commitment to the inputs.
                    input_ids.push(InputID::ExternalRecord(input_commitment));
                }
            }
        }

        // Compute `challenge` as `HashToScalar(r * G, pk_sig, pr_sig, caller, [tvk, input IDs])`.
        let challenge = N::hash_to_scalar_psd8(&preimage)?;
        // Compute `response` as `r - challenge * sk_sig`.
        let response = r - challenge * sk_sig;

        Ok(Self {
            caller,
            network_id: U16::new(N::ID),
            program_id,
            function_name,
            input_ids,
            inputs: inputs.to_vec(),
            signature: Signature::from((challenge, response, compute_key)),
            tvk,
            tsk: r,
        })
    }
}
