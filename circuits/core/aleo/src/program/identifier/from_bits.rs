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

impl<A: Aleo> FromBits for Identifier<A> {
    type Boolean = Boolean<A>;

    /// Initializes a new identifier from little-endian bits.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Recover the field element from the bits.
        let field = Field::from_bits_le(bits_le);
        // Recover the identifier length from the bits.
        let num_bytes = {
            // Eject the bits in **little-endian** form.
            let bits_le = field.to_bits_le().eject_value();
            // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
            let bytes = bits_le
                .chunks(8)
                .map(|byte| match u8::from_bits_le(byte) {
                    Ok(byte) => byte,
                    Err(error) => A::halt(format!("Failed to recover an identifier from bits: {error}")),
                })
                .collect::<Vec<_>>();
            // Find the first instance of a `0` byte, which is the null character '\0' in UTF-8,
            // and an invalid character according to our rules for representing an identifier.
            match bytes.iter().position(|&byte| byte == 0) {
                Some(index) => index,
                None => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
            }
        };
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = A::BaseField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        match num_bytes <= max_bytes {
            // Return the identifier.
            true => Self(field, num_bytes as u8),
            false => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
        }
    }

    /// Initializes a new identifier from big-endian bits.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Recover the field element from the bits.
        let field = Field::from_bits_be(bits_be);
        // Recover the identifier length from the bits.
        let num_bytes = {
            // Eject the bits in **little-endian** form (this is correct for this `from_bits_be` case).
            let bits_le = field.to_bits_le().eject_value();
            // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
            let bytes = bits_le
                .chunks(8)
                .map(|byte| match u8::from_bits_le(byte) {
                    Ok(byte) => byte,
                    Err(error) => A::halt(format!("Failed to recover an identifier from bits: {error}")),
                })
                .collect::<Vec<_>>();
            // Find the first instance of a `0` byte, which is the null character '\0' in UTF-8,
            // and an invalid character according to our rules for representing an identifier.
            match bytes.iter().position(|&byte| byte == 0) {
                Some(index) => index,
                None => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
            }
        };
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = A::BaseField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        match num_bytes <= max_bytes {
            // Return the identifier.
            true => Self(field, num_bytes as u8),
            false => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
        }
    }
}
