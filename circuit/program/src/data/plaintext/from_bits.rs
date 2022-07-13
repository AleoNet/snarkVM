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
        // Interface
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
                Ok(_) => Self::Interface(members, cache),
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
        // Interface
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
                Ok(_) => Self::Interface(members, cache),
                Err(_) => A::halt("Failed to store the plaintext bits in the cache."),
            }
        }
        // Unknown variant.
        else {
            A::halt("Unknown plaintext variant.")
        }
    }
}
