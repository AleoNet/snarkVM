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

impl<N: Network> FromBytes for TransitionProof<N> {
    /// Reads the transition proof from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = Variant::read_le(&mut reader)?;
        let proof = match index {
            0 => Self::new_birth(FromBytes::read_le(&mut reader)?),
            1 => Self::new_birth_and_death(FromBytes::read_le(&mut reader)?, FromBytes::read_le(&mut reader)?),
            2.. => return Err(error(format!("Failed to decode transition proof variant {index}"))),
        };
        Ok(proof)
    }
}

impl<N: Network> ToBytes for TransitionProof<N> {
    /// Writes the transition proof to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Birth(execution) => {
                (0 as Variant).write_le(&mut writer)?;
                execution.write_le(&mut writer)
            }
            TransitionProof::BirthAndDeath { execution_proof, state_path_proof } => {
                (1 as Variant).write_le(&mut writer)?;
                execution_proof.write_le(&mut writer)?;
                state_path_proof.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() {
        // Sample the transition proof.
        let expected = crate::process::test_helpers::sample_transition().proof().clone();

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le().unwrap();
        assert_eq!(expected, TransitionProof::read_le(&expected_bytes[..]).unwrap());
        assert!(TransitionProof::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
    }
}
