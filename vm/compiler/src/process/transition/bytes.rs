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

impl<N: Network> FromBytes for Transition<N> {
    /// Reads the output from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u16::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid transition version"));
        }

        let transition_id = N::TransitionID::read_le(&mut reader)?;
        let program_id = FromBytes::read_le(&mut reader)?;
        let function_name = FromBytes::read_le(&mut reader)?;

        let num_inputs: u16 = FromBytes::read_le(&mut reader)?;
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            inputs.push(FromBytes::read_le(&mut reader)?);
        }

        let num_outputs: u16 = FromBytes::read_le(&mut reader)?;
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            outputs.push(FromBytes::read_le(&mut reader)?);
        }

        let proof = FromBytes::read_le(&mut reader)?;
        let tpk = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;

        // Construct the candidate transition.
        let transition =
            Self::new(program_id, function_name, inputs, outputs, proof, tpk, fee).map_err(|e| error(e.to_string()))?;
        // Ensure the transition ID matches the expected ID.
        match transition_id == *transition.id() {
            true => Ok(transition),
            false => Err(error("Transition ID is incorrect, possible data corruption")),
        }
    }
}

impl<N: Network> ToBytes for Transition<N> {
    /// Writes the literal to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u16.write_le(&mut writer)?;

        self.id.write_le(&mut writer)?;
        self.program_id.write_le(&mut writer)?;
        self.function_name.write_le(&mut writer)?;

        (self.inputs.len() as u16).write_le(&mut writer)?;
        self.inputs.write_le(&mut writer)?;

        (self.outputs.len() as u16).write_le(&mut writer)?;
        self.outputs.write_le(&mut writer)?;

        self.proof.write_le(&mut writer)?;
        self.tpk.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        // Sample the transition.
        let expected = crate::process::test_helpers::sample_transition();

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Transition::read_le(&expected_bytes[..])?);
        assert!(Transition::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());

        Ok(())
    }
}
