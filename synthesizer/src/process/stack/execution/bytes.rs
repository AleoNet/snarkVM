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

impl<N: Network> FromBytes for Execution<N> {
    /// Reads the execution from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u16::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid execution version"));
        }
        // Read the number of transitions.
        let num_transitions = u16::read_le(&mut reader)?;
        // Ensure the number of transitions is nonzero.
        if num_transitions == 0 {
            warn!("Execution (from 'read_le') has no transitions");
            return Err(error("Execution (from 'read_le') has no transitions"));
        }
        // Read the transitions.
        let transitions =
            (0..num_transitions).map(|_| Transition::read_le(&mut reader)).collect::<IoResult<Vec<_>>>()?;
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
        // Return the new `Execution` instance.
        Self::from(transitions.into_iter(), global_state_root, inclusion_proof).map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for Execution<N> {
    /// Writes the execution to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u16.write_le(&mut writer)?;
        // Write the number of transitions.
        (self.transitions.len() as u16).write_le(&mut writer)?;
        // Write the transitions.
        for transition in self.transitions.values() {
            transition.write_le(&mut writer)?;
        }
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
        // Construct a new execution.
        let expected = crate::process::test_helpers::sample_execution();

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Execution::read_le(&expected_bytes[..])?);
        assert!(Execution::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        Ok(())
    }
}
