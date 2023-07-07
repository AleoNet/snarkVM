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

impl<A: Aleo> FromBits for Plaintext<A> {
    type Boolean = Boolean<A>;

    /// Initializes a new plaintext from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Boolean<A>]) -> Self {
        let mut counter = 0;

        let variant = [bits_le[counter].eject_value(), bits_le[counter + 1].eject_value()];
        counter += 2;

        // Literal
        if variant == [false, false] {
            let literal_variant = U8::from_bits_le(&bits_le[counter..counter + 8]);
            counter += 8;

            let literal_size = U16::from_bits_le(&bits_le[counter..counter + 16]).eject_value();
            counter += 16;

            let literal = Literal::from_bits_le(&literal_variant, &bits_le[counter..counter + *literal_size as usize]);

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the literal.
                Ok(_) => Self::Literal(literal, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Struct
        else if variant == [false, true] {
            let num_members = U8::from_bits_le(&bits_le[counter..counter + 8]).eject_value();
            counter += 8;

            let mut members = IndexMap::with_capacity(*num_members as usize);
            for _ in 0..*num_members {
                let identifier_size = U8::from_bits_le(&bits_le[counter..counter + 8]).eject_value();
                counter += 8;

                let identifier = Identifier::from_bits_le(&bits_le[counter..counter + *identifier_size as usize]);
                counter += *identifier_size as usize;

                let member_size = U16::from_bits_le(&bits_le[counter..counter + 16]).eject_value();
                counter += 16;

                let value = Plaintext::from_bits_le(&bits_le[counter..counter + *member_size as usize]);
                counter += *member_size as usize;

                members.insert(identifier, value);
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the member.
                Ok(_) => Self::Struct(members, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Unknown variant.
        else {
            A::halt("Unknown plaintext variant.")
        }
    }

    /// Initializes a new plaintext from a list of big-endian bits *without* trailing zeros.
    fn from_bits_be(bits_be: &[Boolean<A>]) -> Self {
        let mut counter = 0;

        let variant = [bits_be[counter].eject_value(), bits_be[counter + 1].eject_value()];
        counter += 2;

        // Literal
        if variant == [false, false] {
            let literal_variant = U8::from_bits_be(&bits_be[counter..counter + 8]);
            counter += 8;

            let literal_size = U16::from_bits_be(&bits_be[counter..counter + 16]).eject_value();
            counter += 16;

            let literal = Literal::from_bits_be(&literal_variant, &bits_be[counter..counter + *literal_size as usize]);

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the literal.
                Ok(_) => Self::Literal(literal, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Struct
        else if variant == [false, true] {
            let num_members = U8::from_bits_be(&bits_be[counter..counter + 8]).eject_value();
            counter += 8;

            let mut members = IndexMap::with_capacity(*num_members as usize);
            for _ in 0..*num_members {
                let identifier_size = U8::from_bits_be(&bits_be[counter..counter + 8]).eject_value();
                counter += 8;

                let identifier = Identifier::from_bits_be(&bits_be[counter..counter + *identifier_size as usize]);
                counter += *identifier_size as usize;

                let member_size = U16::from_bits_be(&bits_be[counter..counter + 16]).eject_value();
                counter += 16;

                let value = Plaintext::from_bits_be(&bits_be[counter..counter + *member_size as usize]);
                counter += *member_size as usize;

                members.insert(identifier, value);
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the member.
                Ok(_) => Self::Struct(members, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Unknown variant.
        else {
            A::halt("Unknown plaintext variant.")
        }
    }
}
