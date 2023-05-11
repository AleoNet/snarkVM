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

impl<N: Network> FromBytes for Request<N> {
    /// Reads the request from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid request version"));
        }

        // Read the caller.
        let caller = FromBytes::read_le(&mut reader)?;
        // Read the network ID.
        let network_id = FromBytes::read_le(&mut reader)?;
        // Read the program ID.
        let program_id = FromBytes::read_le(&mut reader)?;
        // Read the function name.
        let function_name = FromBytes::read_le(&mut reader)?;

        // Read the number of inputs.
        let inputs_len = u16::read_le(&mut reader)?;
        // Read the input IDs.
        let input_ids = (0..inputs_len).map(|_| FromBytes::read_le(&mut reader)).collect::<Result<Vec<_>, _>>()?;
        // Read the inputs.
        let inputs = (0..inputs_len).map(|_| FromBytes::read_le(&mut reader)).collect::<Result<Vec<_>, _>>()?;

        // Read the signature.
        let signature = FromBytes::read_le(&mut reader)?;
        // Read the tag secret key.
        let sk_tag = FromBytes::read_le(&mut reader)?;
        // Read the transition view key.
        let tvk = FromBytes::read_le(&mut reader)?;
        // Read the transition secret key.
        let tsk = FromBytes::read_le(&mut reader)?;
        // Read the transition commitment.
        let tcm = FromBytes::read_le(&mut reader)?;

        Ok(Self::from((
            caller,
            network_id,
            program_id,
            function_name,
            input_ids,
            inputs,
            signature,
            sk_tag,
            tvk,
            tsk,
            tcm,
        )))
    }
}

impl<N: Network> ToBytes for Request<N> {
    /// Writes the request to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;

        // Write the caller.
        self.caller.write_le(&mut writer)?;
        // Write the network ID.
        self.network_id.write_le(&mut writer)?;
        // Write the program ID.
        self.program_id.write_le(&mut writer)?;
        // Write the function name.
        self.function_name.write_le(&mut writer)?;

        // Ensure the input IDs and inputs are the same length.
        if self.input_ids.len() != self.inputs.len() {
            return Err(error("Invalid request: mismatching number of input IDs and inputs"));
        }

        // Write the number of inputs.
        u16::try_from(self.input_ids.len())
            .or_halt_with::<N>("Request inputs length exceeds u16")
            .write_le(&mut writer)?;
        // Write the input IDs.
        for input_id in &self.input_ids {
            input_id.write_le(&mut writer)?;
        }
        // Write the inputs.
        for input in &self.inputs {
            input.write_le(&mut writer)?;
        }

        // Write the signature.
        self.signature.write_le(&mut writer)?;
        // Write the tag secret key.
        self.sk_tag.write_le(&mut writer)?;
        // Write the transition view key.
        self.tvk.write_le(&mut writer)?;
        // Write the transition secret key.
        self.tsk.write_le(&mut writer)?;
        // Write the transition commitment.
        self.tcm.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() {
        let mut rng = TestRng::default();

        for expected in test_helpers::sample_requests(&mut rng).into_iter() {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, Request::read_le(&expected_bytes[..]).unwrap());
            assert!(Request::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
