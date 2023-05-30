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

impl<N: Network> FromBits for Plaintext<N> {
    /// Initializes a new plaintext from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        let mut counter = 0;

        let variant = [bits_le[counter], bits_le[counter + 1]];
        counter += 2;

        // Literal
        if variant == [false, false] {
            let literal_variant = u8::from_bits_le(&bits_le[counter..counter + 8])?;
            counter += 8;

            let literal_size = u16::from_bits_le(&bits_le[counter..counter + 16])?;
            counter += 16;

            let literal = Literal::from_bits_le(literal_variant, &bits_le[counter..counter + literal_size as usize])?;

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the literal.
                Ok(_) => Ok(Self::Literal(literal, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
        // Struct
        else if variant == [false, true] {
            let num_members = u8::from_bits_le(&bits_le[counter..counter + 8])?;
            counter += 8;

            let mut members = IndexMap::with_capacity(num_members as usize);
            for _ in 0..num_members {
                let identifier_size = u8::from_bits_le(&bits_le[counter..counter + 8])?;
                counter += 8;

                let identifier = Identifier::from_bits_le(&bits_le[counter..counter + identifier_size as usize])?;
                counter += identifier_size as usize;

                let member_size = u16::from_bits_le(&bits_le[counter..counter + 16])?;
                counter += 16;

                let value = Plaintext::from_bits_le(&bits_le[counter..counter + member_size as usize])?;
                counter += member_size as usize;

                if members.insert(identifier, value).is_some() {
                    bail!("Duplicate identifier in struct.");
                }
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_le.to_vec()) {
                // Return the struct.
                Ok(_) => Ok(Self::Struct(members, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
        // Unknown variant.
        else {
            bail!("Unknown plaintext variant.");
        }
    }

    /// Initializes a new plaintext from a list of big-endian bits *without* trailing zeros.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        let mut counter = 0;

        let variant = [bits_be[counter], bits_be[counter + 1]];
        counter += 2;

        // Literal
        if variant == [false, false] {
            let literal_variant = u8::from_bits_be(&bits_be[counter..counter + 8])?;
            counter += 8;

            let literal_size = u16::from_bits_be(&bits_be[counter..counter + 16])?;
            counter += 16;

            let literal = Literal::from_bits_be(literal_variant, &bits_be[counter..counter + literal_size as usize])?;

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the literal.
                Ok(_) => Ok(Self::Literal(literal, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
        // Struct
        else if variant == [false, true] {
            let num_members = u8::from_bits_be(&bits_be[counter..counter + 8])?;
            counter += 8;

            let mut members = IndexMap::with_capacity(num_members as usize);
            for _ in 0..num_members {
                let identifier_size = u8::from_bits_be(&bits_be[counter..counter + 8])?;
                counter += 8;

                let identifier = Identifier::from_bits_be(&bits_be[counter..counter + identifier_size as usize])?;
                counter += identifier_size as usize;

                let member_size = u16::from_bits_be(&bits_be[counter..counter + 16])?;
                counter += 16;

                let value = Plaintext::from_bits_be(&bits_be[counter..counter + member_size as usize])?;
                counter += member_size as usize;

                if members.insert(identifier, value).is_some() {
                    bail!("Duplicate identifier in struct.");
                }
            }

            // Store the plaintext bits in the cache.
            let cache = OnceCell::new();
            match cache.set(bits_be.to_vec()) {
                // Return the struct.
                Ok(_) => Ok(Self::Struct(members, cache)),
                Err(_) => bail!("Failed to store the plaintext bits in the cache."),
            }
        }
        // Unknown variant.
        else {
            bail!("Unknown plaintext variant.");
        }
    }
}
