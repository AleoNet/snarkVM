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

impl<N: Network> FromBytes for Deployment<N> {
    /// Reads the deployment from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 1 {
            return Err(error("Invalid deployment version"));
        }

        // Read the edition.
        let edition = u16::read_le(&mut reader)?;
        // Read the program.
        let program = Program::read_le(&mut reader)?;

        // Read the number of entries in the bundle.
        let num_entries = u16::read_le(&mut reader)?;
        // Read the function specifications.
        let mut function_specs = Vec::with_capacity(num_entries as usize);
        for _ in 0..num_entries {
            // Read the identifier.
            let identifier = Identifier::<N>::read_le(&mut reader)?;
            // Read the verifying key.
            let verifying_key = VerifyingKey::<N>::read_le(&mut reader)?;
            // Read the certificate.
            let certificate = Certificate::<N>::read_le(&mut reader)?;
            // Read the variable count.
            let variable_count = u64::read_le(&mut reader)?;
            // Add the entry.
            function_specs.push((identifier, (verifying_key, certificate, variable_count)));
        }

        // Return the deployment.
        Self::new(edition, program, function_specs).map_err(|err| error(format!("{err}")))
    }
}

impl<N: Network> ToBytes for Deployment<N> {
    /// Writes the deployment to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        1u8.write_le(&mut writer)?;
        // Write the edition.
        self.edition.write_le(&mut writer)?;
        // Write the program.
        self.program.write_le(&mut writer)?;
        // Write the number of entries in the bundle.
        (u16::try_from(self.function_specs.len()).map_err(|e| error(e.to_string()))?).write_le(&mut writer)?;
        // Write each entry.
        for (function_name, (verifying_key, certificate, variable_count)) in &self.function_specs {
            // Write the function name.
            function_name.write_le(&mut writer)?;
            // Write the verifying key.
            verifying_key.write_le(&mut writer)?;
            // Write the certificate.
            certificate.write_le(&mut writer)?;
            // Write the variable count.
            variable_count.write_le(&mut writer)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut TestRng::default();

        // Construct a new deployment.
        let expected = test_helpers::sample_deployment(rng);

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Deployment::read_le(&expected_bytes[..])?);
        Ok(())
    }
}
