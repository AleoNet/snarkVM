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

impl<N: Network> FromBytes for Fee<N> {
    /// Reads the fee from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid fee version"));
        }
        // Read the transition.
        let transition = Transition::read_le(&mut reader)?;
        // Read the global state root.
        let global_state_root = N::StateRoot::read_le(&mut reader)?;
        // Read the inclusion proof variant.
        let inclusion_variant = u8::read_le(&mut reader)?;
        // Read the inclusion proof.
        let inclusion_proof = match inclusion_variant {
            0 => None,
            1 => Some(Proof::read_le(&mut reader)?),
            _ => return Err(error("Invalid inclusion proof variant '{inclusion_variant}'")),
        };
        // Return the new `Fee` instance.
        Ok(Self::from(transition, global_state_root, inclusion_proof))
    }
}

impl<N: Network> ToBytes for Fee<N> {
    /// Writes the fee to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;
        // Write the transition.
        self.transition.write_le(&mut writer)?;
        // Write the global state root.
        self.global_state_root.write_le(&mut writer)?;
        // Write the inclusion proof.
        match self.inclusion_proof {
            None => 0u8.write_le(&mut writer)?,
            Some(ref proof) => {
                1u8.write_le(&mut writer)?;
                proof.write_le(&mut writer)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut TestRng::default();

        // Construct a new fee.
        let expected = crate::vm::test_helpers::sample_fee(rng);

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Fee::read_le(&expected_bytes[..])?);
        assert!(Fee::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        Ok(())
    }
}
