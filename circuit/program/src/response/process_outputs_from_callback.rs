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
    /// Returns the injected circuit outputs, given the number of inputs, caller, tvk, outputs, and output types.
    pub fn process_outputs_from_callback(
        program_id: &ProgramID<A>,
        num_inputs: usize,
        tvk: &Field<A>,
        outputs: Vec<console::Value<A::Network>>,        // Note: Console type
        output_types: &[console::ValueType<A::Network>], // Note: Console type
    ) -> Vec<Value<A>> {
        match outputs
            .iter()
            .zip_eq(output_types)
            .enumerate()
            .map(|(index, (output, output_types))| {
                match output_types {
                    // For a constant output, compute the hash of the output.
                    console::ValueType::Constant(..) => {
                        // Inject the output as `Mode::Constant`.
                        let output = Value::new(Mode::Constant, output.clone());
                        // Ensure the output is a plaintext.
                        ensure!(matches!(output, Value::Plaintext(..)), "Expected a plaintext output");

                        // Hash the output to a field element.
                        let output_hash = A::hash_bhp1024(&output.to_bits_le());
                        // Return the output ID.
                        Ok((OutputID::constant(output_hash), output))
                    }
                    // For a public output, compute the hash of the output.
                    console::ValueType::Public(..) => {
                        // Inject the output as `Mode::Private`.
                        let output = Value::new(Mode::Private, output.clone());
                        // Ensure the output is a plaintext.
                        ensure!(matches!(output, Value::Plaintext(..)), "Expected a plaintext output");

                        // Hash the output to a field element.
                        let output_hash = A::hash_bhp1024(&output.to_bits_le());
                        // Return the output ID.
                        Ok((OutputID::public(output_hash), output))
                    }
                    // For a private output, compute the ciphertext (using `tvk`) and hash the ciphertext.
                    console::ValueType::Private(..) => {
                        // Inject the output as `Mode::Private`.
                        let output = Value::new(Mode::Private, output.clone());
                        // Ensure the output is a plaintext.
                        ensure!(matches!(output, Value::Plaintext(..)), "Expected a plaintext output");

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
                        Ok((OutputID::private(output_hash), output))
                    }
                    // For a record output, compute the record commitment, and encrypt the record (using `tvk`).
                    console::ValueType::Record(record_name) => {
                        // Inject the output as `Mode::Private`.
                        let output = Value::new(Mode::Private, output.clone());

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

                        // Return the output ID.
                        // Note: Because this is a callback, the output ID is **only** the record commitment.
                        Ok((OutputID::external_record(commitment), output))
                    }
                    // For an external record output, compute the commitment (using `tvk`) of the output.
                    console::ValueType::ExternalRecord(..) => {
                        // Inject the output as `Mode::Private`.
                        let output = Value::new(Mode::Private, output.clone());
                        // Ensure the output is a record.
                        ensure!(matches!(output, Value::Record(..)), "Expected a record output");

                        // Prepare the index as a constant field element.
                        let output_index = Field::constant(console::Field::from_u16((num_inputs + index) as u16));
                        // Compute the commitment randomizer as `HashToScalar(tvk || index)`.
                        let randomizer = A::hash_to_scalar_psd2(&[tvk.clone(), output_index]);
                        // Commit the output to a field element.
                        let commitment = A::commit_bhp1024(&output.to_bits_le(), &randomizer);
                        // Return the output ID.
                        Ok((OutputID::external_record(commitment), output))
                    }
                }
            })
            .collect::<Result<Vec<_>>>()
        {
            Ok(outputs) => {
                // Unzip the output IDs from the output values.
                let (_, outputs): (Vec<OutputID<A>>, _) = outputs.into_iter().unzip();
                // Return the outputs.
                outputs
            }
            Err(error) => A::halt(error.to_string()),
        }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_crypto_rng, Uniform};

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 20;

    fn check_from_callback(
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

            // Inject the program ID and `tvk`.
            let program_id = ProgramID::<Circuit>::new(mode, program_id);
            let tvk = Field::<Circuit>::new(mode, tvk);

            Circuit::scope(format!("Response {i}"), || {
                let outputs = Response::process_outputs_from_callback(
                    &program_id,
                    4,
                    &tvk,
                    response.outputs().to_vec(),
                    &output_types,
                );
                assert_eq!(response.outputs(), outputs.eject_value());
                match mode.is_constant() {
                    true => assert_scope!(<=num_constants, <=num_public, <=num_private, <=num_constraints),
                    false => assert_scope!(<=num_constants, num_public, num_private, num_constraints),
                }
            });

            // Compute the response using outputs (circuit).
            let outputs = Inject::new(mode, response.outputs().to_vec());
            let candidate_b = Response::from_outputs(&program_id, 4, &tvk, outputs, &output_types);
            assert_eq!(response, candidate_b.eject_value());

            Circuit::reset();
        }
        Ok(())
    }

    // Note: These counts are correct. At this (high) level of a program, we override the default mode in many cases,
    // based on the user-defined visibility in the types. Thus, we have nonzero public, private, and constraint values.

    #[test]
    fn test_from_callback_constant() -> Result<()> {
        check_from_callback(Mode::Constant, 19500, 4, 5050, 5050)
    }

    #[test]
    fn test_from_callback_public() -> Result<()> {
        check_from_callback(Mode::Public, 19310, 4, 8962, 8970)
    }

    #[test]
    fn test_from_callback_private() -> Result<()> {
        check_from_callback(Mode::Private, 19310, 4, 8962, 8970)
    }
}
