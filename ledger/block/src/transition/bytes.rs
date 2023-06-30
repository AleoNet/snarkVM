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

impl<N: Network> FromBytes for Transition<N> {
    /// Reads the output from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid transition version"));
        }

        // Read the transition ID.
        let transition_id = N::TransitionID::read_le(&mut reader)?;
        // Read the program ID.
        let program_id = FromBytes::read_le(&mut reader)?;
        // Read the function name.
        let function_name = FromBytes::read_le(&mut reader)?;

        // Read the number of inputs.
        let num_inputs: u8 = FromBytes::read_le(&mut reader)?;
        // Read the inputs.
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            // Read the input.
            inputs.push(FromBytes::read_le(&mut reader)?);
        }

        // Read the number of outputs.
        let num_outputs: u8 = FromBytes::read_le(&mut reader)?;
        // Read the outputs.
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            // Read the output.
            outputs.push(FromBytes::read_le(&mut reader)?);
        }

        // Read the finalize variant.
        let finalize_variant = u8::read_le(&mut reader)?;
        // Read the finalize inputs.
        let finalize = match finalize_variant {
            0 => None,
            1 => {
                // Read the number of inputs for finalize.
                let num_finalize_inputs = u8::read_le(&mut reader)?;
                // Read the inputs for finalize.
                let mut finalize = Vec::with_capacity(num_finalize_inputs as usize);
                for _ in 0..num_finalize_inputs {
                    // Read the input for finalize.
                    finalize.push(FromBytes::read_le(&mut reader)?);
                }
                Some(finalize)
            }
            2.. => return Err(error(format!("Invalid transition finalize variant ({finalize_variant})"))),
        };

        // Read the transition public key.
        let tpk = FromBytes::read_le(&mut reader)?;
        // Read the transition commitment.
        let tcm = FromBytes::read_le(&mut reader)?;

        // Construct the candidate transition.
        let transition = Self::new(program_id, function_name, inputs, outputs, finalize, tpk, tcm)
            .map_err(|e| error(e.to_string()))?;
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
        0u8.write_le(&mut writer)?;

        // Write the transition ID.
        self.id.write_le(&mut writer)?;
        // Write the program ID.
        self.program_id.write_le(&mut writer)?;
        // Write the function name.
        self.function_name.write_le(&mut writer)?;

        // Write the number of inputs.
        (u8::try_from(self.inputs.len()).map_err(|e| error(e.to_string()))?).write_le(&mut writer)?;
        // Write the inputs.
        self.inputs.write_le(&mut writer)?;

        // Write the number of outputs.
        (u8::try_from(self.outputs.len()).map_err(|e| error(e.to_string()))?).write_le(&mut writer)?;
        // Write the outputs.
        self.outputs.write_le(&mut writer)?;

        // Write the finalize inputs.
        match &self.finalize {
            None => {
                // Write the finalize variant.
                0u8.write_le(&mut writer)?;
            }
            Some(finalize) => {
                // Write the finalize variant.
                1u8.write_le(&mut writer)?;
                // Write the number of inputs to finalize.
                (u8::try_from(finalize.len()).map_err(|e| error(e.to_string()))?).write_le(&mut writer)?;
                // Write the inputs to finalize.
                finalize.write_le(&mut writer)?;
            }
        }

        // Write the transition public key.
        self.tpk.write_le(&mut writer)?;
        // Write the transition commitment.
        self.tcm.write_le(&mut writer)
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

        // Sample the transition.
        let expected = crate::test_helpers::sample_transition(rng);

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Transition::read_le(&expected_bytes[..])?);
        assert!(Transition::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());

        Ok(())
    }
}
