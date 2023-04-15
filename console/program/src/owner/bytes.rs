// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> FromBytes for ProgramOwner<N> {
    /// Reads the program owner from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid program owner version"));
        }

        // Read the address.
        let address = Address::read_le(&mut reader)?;
        // Read the signature.
        let signature = Signature::read_le(&mut reader)?;

        // Return the program owner.
        Ok(Self::from(address, signature))
    }
}

impl<N: Network> ToBytes for ProgramOwner<N> {
    /// Writes the program owner to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;
        // Write the address.
        self.address.write_le(&mut writer)?;
        // Write the signature.
        self.signature.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        // Construct a new program owner.
        let expected = test_helpers::sample_program_owner();

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, ProgramOwner::read_le(&expected_bytes[..])?);
        assert!(ProgramOwner::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        Ok(())
    }
}
