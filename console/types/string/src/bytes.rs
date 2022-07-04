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

impl<E: Environment> FromBytes for StringType<E> {
    /// Reads the string from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of bytes.
        let num_bytes = u16::read_le(&mut reader)?;
        // Ensure the number of bytes is within the allowed bounds.
        if num_bytes as u32 > E::MAX_STRING_BYTES {
            return Err(error(format!("String literal exceeds maximum length of {} bytes.", E::MAX_STRING_BYTES)));
        }
        // Read the bytes.
        let mut bytes = vec![0u8; num_bytes as usize];
        reader.read_exact(&mut bytes)?;
        // Return the string.
        Ok(Self::new(&String::from_utf8(bytes).map_err(|e| error(e.to_string()))?))
    }
}

impl<E: Environment> ToBytes for StringType<E> {
    /// Writes the string to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of bytes is within the allowed bounds.
        if self.string.len() > E::MAX_STRING_BYTES as usize {
            return Err(error(format!("String literal exceeds maximum length of {} bytes.", E::MAX_STRING_BYTES)));
        }
        // Write the number of bytes.
        (self.string.len() as u16).write_le(&mut writer)?;
        // Write the bytes.
        self.string.as_bytes().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_bytes() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new string.
            let expected = StringType::<CurrentEnvironment>::rand(&mut test_rng());

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, StringType::read_le(&expected_bytes[..])?);
            assert!(StringType::<CurrentEnvironment>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
