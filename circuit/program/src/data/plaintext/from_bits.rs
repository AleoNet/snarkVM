// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use crate::ProgramID;

impl<A: Aleo> FromBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Initializes a new plaintext from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Boolean<A>]) -> Self {
        let bits = bits_le;

        // The starting index used to create subsequent subslices of the `bits` slice.
        let mut index = 0;

        // Helper function to get the next n bits as a slice.
        let mut next_bits = |n: usize| -> &[Boolean<A>] {
            // Safely procure a subslice with the length `n` starting at `index`.
            let subslice = bits.get(index..index + n);
            // Check if the range is within bounds.
            if let Some(next_bits) = subslice {
                // Move the starting index.
                index += n;
                // Return the subslice.
                next_bits
            } else {
                A::halt("Insufficient bits.")
            }
        };

        let mut variant = next_bits(2).iter().map(|b| b.eject_value());
        let variant1 = variant.next().unwrap();
        let variant2 = variant.next().unwrap();
        let variant = [variant1, variant2];

        // Literal
        if variant == [false, false] {
            let literal_variant = U8::from_bits_le(next_bits(8));
            let literal_size = U16::from_bits_le(next_bits(16)).eject_value();
            let literal = Literal::from_bits_le(&literal_variant, next_bits(*literal_size as usize));

            // Cache the plaintext bits, and return the literal.
            Self::Literal(literal, OnceCell::with_value(bits_le.to_vec()))
        }
        // Struct
        else if variant == [false, true] {
            let num_members = U8::from_bits_le(next_bits(8)).eject_value();

            let mut members = IndexMap::with_capacity(*num_members as usize);
            for _ in 0..*num_members {
                let identifier_size = U8::from_bits_le(next_bits(8)).eject_value();
                let identifier = Identifier::from_bits_le(next_bits(*identifier_size as usize));

                let member_size = U16::from_bits_le(next_bits(16)).eject_value();
                let value = Plaintext::from_bits_le(next_bits(*member_size as usize));

                members.insert(identifier, value);
            }

            // Cache the plaintext bits, and return the struct.
            Self::Struct(members, OnceCell::with_value(bits_le.to_vec()))
        }
        // Array
        else if variant == [true, false] {
            let num_elements = U32::from_bits_le(next_bits(32)).eject_value();

            let mut elements = Vec::with_capacity(*num_elements as usize);
            for _ in 0..*num_elements {
                let element_size = U16::from_bits_le(next_bits(16)).eject_value();
                let value = Plaintext::from_bits_le(next_bits(*element_size as usize));

                elements.push(value);
            }

            // Cache the plaintext bits, and return the array.
            Self::Array(elements, OnceCell::with_value(bits_le.to_vec()))
        }
        // Future
        else if variant == [true, true] {
            // Read the program ID name.
            let program_id_name_size = U8::from_bits_le(next_bits(8)).eject_value();
            let program_id_name = Identifier::from_bits_le(next_bits(*program_id_name_size as usize));
            // Read the program ID network.
            let program_id_network_size = U8::from_bits_le(next_bits(8)).eject_value();
            let program_id_network = Identifier::from_bits_le(next_bits(*program_id_network_size as usize));
            // Initialize the program ID.
            let program_id =
                match console::ProgramID::try_from((program_id_name.eject_value(), program_id_network.eject_value())) {
                    Ok(program_id) => ProgramID::<A>::new(Mode::Constant, program_id),
                    Err(_) => A::halt("Invalid program ID."),
                };

            // Read the function name.
            let function_name_size = U8::from_bits_le(next_bits(8)).eject_value();
            let function_name = Identifier::from_bits_le(next_bits(*function_name_size as usize));

            // Read the inputs.
            let num_inputs = U8::from_bits_le(next_bits(8)).eject_value();
            let mut inputs = Vec::with_capacity(*num_inputs as usize);
            for _ in 0..*num_inputs {
                let input_size = U16::from_bits_le(next_bits(16)).eject_value();
                let input = Plaintext::from_bits_le(next_bits(*input_size as usize));
                inputs.push(input);
            }
            // Cache the plaintext bits, and return the future.
            Self::Future(
                Future::new(
                    Mode::Public,
                    console::Future::new(program_id.eject_value(), function_name.eject_value(), inputs.eject_value()),
                ),
                OnceCell::with_value(bits_le.to_vec()),
            )
        }
        // Unknown variant.
        else {
            A::halt("Unknown plaintext variant.")
        }
    }

    /// Initializes a new plaintext from a list of big-endian bits *without* trailing zeros.
    fn from_bits_be(bits_be: &[Boolean<A>]) -> Self {
        let bits = bits_be;

        // The starting index used to create subsequent subslices of the `bits` slice.
        let mut index = 0;

        // Helper function to get the next n bits as a slice.
        let mut next_bits = |n: usize| -> &[Boolean<A>] {
            // Safely procure a subslice with the length `n` starting at `index`.
            let subslice = bits.get(index..index + n);
            // Check if the range is within bounds.
            if let Some(next_bits) = subslice {
                // Move the starting index.
                index += n;
                // Return the subslice.
                next_bits
            } else {
                A::halt("Insufficient bits.")
            }
        };

        let mut variant = next_bits(2).iter().map(|b| b.eject_value());
        let variant1 = variant.next().unwrap();
        let variant2 = variant.next().unwrap();
        let variant = [variant1, variant2];

        // Literal
        if variant == [false, false] {
            let literal_variant = U8::from_bits_be(next_bits(8));
            let literal_size = U16::from_bits_be(next_bits(16)).eject_value();
            let literal = Literal::from_bits_be(&literal_variant, next_bits(*literal_size as usize));

            // Cache the plaintext bits, and return the literal.
            Self::Literal(literal, OnceCell::with_value(bits_be.to_vec()))
        }
        // Struct
        else if variant == [false, true] {
            let num_members = U8::from_bits_be(next_bits(8)).eject_value();

            let mut members = IndexMap::with_capacity(*num_members as usize);
            for _ in 0..*num_members {
                let identifier_size = U8::from_bits_be(next_bits(8)).eject_value();
                let identifier = Identifier::from_bits_be(next_bits(*identifier_size as usize));

                let member_size = U16::from_bits_be(next_bits(16)).eject_value();
                let value = Plaintext::from_bits_be(next_bits(*member_size as usize));

                members.insert(identifier, value);
            }

            // Cache the plaintext bits, and return the struct.
            Self::Struct(members, OnceCell::with_value(bits_be.to_vec()))
        }
        // Array
        else if variant == [true, false] {
            let num_elements = U32::from_bits_be(next_bits(32)).eject_value();

            let mut elements = Vec::with_capacity(*num_elements as usize);
            for _ in 0..*num_elements {
                let element_size = U16::from_bits_be(next_bits(16)).eject_value();
                let value = Plaintext::from_bits_be(next_bits(*element_size as usize));

                elements.push(value);
            }

            // Cache the plaintext bits, and return the array.
            Self::Array(elements, OnceCell::with_value(bits_be.to_vec()))
        }
        // Future
        else if variant == [true, true] {
            // Read the program ID name.
            let program_id_name_size = U8::from_bits_be(next_bits(8)).eject_value();
            let program_id_name = Identifier::from_bits_be(next_bits(*program_id_name_size as usize));
            // Read the program ID network.
            let program_id_network_size = U8::from_bits_be(next_bits(8)).eject_value();
            let program_id_network = Identifier::from_bits_be(next_bits(*program_id_network_size as usize));
            // Initialize the program ID.
            let program_id =
                match console::ProgramID::try_from((program_id_name.eject_value(), program_id_network.eject_value())) {
                    Ok(program_id) => ProgramID::<A>::new(Mode::Constant, program_id),
                    Err(_) => A::halt("Invalid program ID."),
                };

            // Read the function name.
            let function_name_size = U8::from_bits_be(next_bits(8)).eject_value();
            let function_name = Identifier::from_bits_be(next_bits(*function_name_size as usize));

            // Read the inputs.
            let num_inputs = U8::from_bits_be(next_bits(8)).eject_value();
            let mut inputs = Vec::with_capacity(*num_inputs as usize);

            for _ in 0..*num_inputs {
                let input_size = U16::from_bits_be(next_bits(16)).eject_value();
                let input = Plaintext::from_bits_be(next_bits(*input_size as usize));
                inputs.push(input);
            }

            // Cache the plaintext bits, and return the future.
            Self::Future(
                Future::new(
                    Mode::Public,
                    console::Future::new(program_id.eject_value(), function_name.eject_value(), inputs.eject_value()),
                ),
                OnceCell::with_value(bits_be.to_vec()),
            )
        }
        // Unknown variant.
        else {
            A::halt("Unknown plaintext variant.")
        }
    }
}
