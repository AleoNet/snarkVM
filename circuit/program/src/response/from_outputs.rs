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

impl<A: Aleo> Response<A> {
    /// Initializes a response, given the number of inputs, caller, tvk, outputs, and output types.
    pub fn from_outputs(
        program_id: &ProgramID<A>,
        num_inputs: usize,
        tvk: &Field<A>,
        outputs: Vec<Value<A>>,
        output_types: &[console::ValueType<A::Network>], // Note: Console type
    ) -> Self {
        // Compute the output IDs.
        let output_ids = outputs
            .iter()
            .zip_eq(output_types)
            .enumerate()
            .map(|(index, (output, output_types))| {
                match output_types {
                    // For a constant output, compute the hash of the output.
                    console::ValueType::Constant(..) => {
                        // Hash the output to a field element.
                        let output_hash = match &output {
                            Value::Plaintext(plaintext) => A::hash_bhp1024(&plaintext.to_bits_le()),
                            // Ensure the output is a plaintext.
                            Value::Record(..) => A::halt("Expected a plaintext output, found a record output"),
                        };
                        // Return the output ID.
                        OutputID::constant(output_hash)
                    }
                    // For a public output, compute the hash of the output.
                    console::ValueType::Public(..) => {
                        // Hash the output to a field element.
                        let output_hash = match &output {
                            Value::Plaintext(plaintext) => A::hash_bhp1024(&plaintext.to_bits_le()),
                            // Ensure the output is a plaintext.
                            Value::Record(..) => A::halt("Expected a plaintext output, found a record output"),
                        };
                        // Return the output ID.
                        OutputID::public(output_hash)
                    }
                    // For a private output, compute the ciphertext (using `tvk`) and hash the ciphertext.
                    console::ValueType::Private(..) => {
                        // Prepare the index as a constant field element.
                        let output_index = Field::constant(console::Field::from_u16((num_inputs + index) as u16));
                        // Compute the output view key as `Hash(tvk || index)`.
                        let output_view_key = A::hash_psd2(&[tvk.clone(), output_index]);
                        // Compute the ciphertext.
                        let ciphertext = match &output {
                            Value::Plaintext(plaintext) => plaintext.encrypt_symmetric(output_view_key),
                            // Ensure the output is a plaintext.
                            Value::Record(..) => A::halt("Expected a plaintext output, found a record output"),
                        };
                        // Hash the ciphertext to a field element.
                        let output_hash = A::hash_bhp1024(&ciphertext.to_bits_le());
                        // Return the output ID.
                        OutputID::private(output_hash)
                    }
                    // For a record output, compute the record commitment, and encrypt the record (using `tvk`).
                    console::ValueType::Record(record_name) => {
                        // Retrieve the record.
                        let record = match &output {
                            Value::Record(record) => record,
                            // Ensure the output is a record.
                            Value::Plaintext(..) => A::halt("Expected a record output, found a plaintext output"),
                        };

                        // Prepare the index as a constant field element.
                        let output_index = Field::constant(console::Field::from_u16((num_inputs + index) as u16));
                        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
                        let randomizer = A::hash_to_scalar_psd2(&[tvk.clone(), output_index]);
                        // Compute the record commitment.
                        let commitment =
                            record.to_commitment(program_id, &Identifier::constant(*record_name), &randomizer);

                        // Compute the record nonce.
                        let nonce = A::g_scalar_multiply(&randomizer).to_x_coordinate();

                        // Encrypt the record, using the randomizer.
                        let encrypted_record = record.encrypt(&randomizer);
                        // Compute the record checksum, as the hash of the encrypted record.
                        let checksum = A::hash_bhp1024(&encrypted_record.to_bits_le());

                        // Return the output ID.
                        OutputID::record(commitment, nonce, checksum)
                    }
                    // For an external record output, compute the commitment (using `tvk`) of the output.
                    console::ValueType::ExternalRecord(..) => {
                        // Prepare the index as a constant field element.
                        let output_index = Field::constant(console::Field::from_u16((num_inputs + index) as u16));
                        // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                        let randomizer = A::hash_to_scalar_psd2(&[tvk.clone(), output_index]);
                        // Commit the output to a field element.
                        let commitment = A::commit_bhp1024(&output.to_bits_le(), &randomizer);
                        // Return the output ID.
                        OutputID::external_record(commitment)
                    }
                }
            })
            .collect();

        // Return the response.
        Self { output_ids, outputs }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_crypto_rng, Uniform};

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 20;

    fn check_from_outputs(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        let rng = &mut test_crypto_rng();

        for i in 0..ITERATIONS {
            // Construct four outputs.
            let output_constant = console::Value::<<Circuit as Environment>::Network>::Plaintext(
                console::Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap(),
            );
            let output_public = console::Value::<<Circuit as Environment>::Network>::Plaintext(
                console::Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap(),
            );
            let output_private = console::Value::<<Circuit as Environment>::Network>::Plaintext(
                console::Plaintext::from_str("{ token_amount: 9876543210u128 }").unwrap(),
            );
            let output_record = console::Value::<<Circuit as Environment>::Network>::Record(console::Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, gates: 5u64.private, token_amount: 100u64.private }").unwrap());
            let output_external_record = console::Value::<<Circuit as Environment>::Network>::Record(console::Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, gates: 5u64.private, token_amount: 100u64.private }").unwrap());
            let outputs = vec![output_constant, output_public, output_private, output_record, output_external_record];

            // Construct the output types.
            let output_types = vec![
                console::ValueType::from_str("amount.constant").unwrap(),
                console::ValueType::from_str("amount.public").unwrap(),
                console::ValueType::from_str("amount.private").unwrap(),
                console::ValueType::from_str("token.record").unwrap(),
                console::ValueType::from_str("token.aleo/token.record").unwrap(),
            ];

            // Sample a `tvk`.
            let tvk = Uniform::rand(rng);

            // Construct a program ID.
            let program_id = console::ProgramID::from_str("test.aleo")?;

            // Construct the response.
            let response = console::Response::new(&program_id, 4, &tvk, outputs.clone(), &output_types)?;
            // assert!(response.verify());

            // Inject the program ID, `tvk`, and outputs.
            let program_id = ProgramID::<Circuit>::new(mode, program_id);
            let tvk = Field::<Circuit>::new(mode, tvk);
            let outputs = Inject::new(mode, outputs);

            Circuit::scope(format!("Response {i}"), || {
                // Compute the response using outputs (circuit).
                let candidate = Response::from_outputs(&program_id, 4, &tvk, outputs, &output_types);
                assert_eq!(response, candidate.eject_value());
                match mode.is_constant() {
                    true => assert_scope!(<=num_constants, <=num_public, <=num_private, <=num_constraints),
                    false => assert_scope!(<=num_constants, num_public, num_private, num_constraints),
                }
            });
            Circuit::reset();
        }
        Ok(())
    }

    // Note: These counts are correct. At this (high) level of a program, we override the default mode in many cases,
    // based on the user-defined visibility in the types. Thus, we have nonzero public, private, and constraint values.

    #[test]
    fn test_from_outputs_constant() -> Result<()> {
        check_from_outputs(Mode::Constant, 23500, 6, 8400, 8400)
    }

    #[test]
    fn test_from_outputs_public() -> Result<()> {
        check_from_outputs(Mode::Public, 21351, 6, 15775, 15792)
    }

    #[test]
    fn test_from_outputs_private() -> Result<()> {
        check_from_outputs(Mode::Private, 21351, 6, 15775, 15792)
    }
}
