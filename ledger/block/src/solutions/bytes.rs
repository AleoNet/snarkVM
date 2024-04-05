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

impl<N: Network> FromBytes for Solutions<N> {
    /// Reads the solutions from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version: u8 = FromBytes::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 1 {
            return Err(error(format!("Invalid solutions version ({version})")));
        }

        // Read the variant.
        let variant: u8 = FromBytes::read_le(&mut reader)?;
        // Parse the variant.
        match variant {
            0 => {
                // Return the solutions.
                Ok(Self { solutions: None })
            }
            1 => {
                // Read the solutions.
                let solutions: PuzzleSolutions<N> = FromBytes::read_le(&mut reader)?;
                // Return the solutions.
                Self::new(solutions).map_err(error)
            }
            _ => Err(error(format!("Invalid solutions variant ({variant})"))),
        }
    }
}

impl<N: Network> ToBytes for Solutions<N> {
    /// Writes the solutions to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        1u8.write_le(&mut writer)?;

        match &self.solutions {
            None => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
            }
            Some(solutions) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the solutions.
                solutions.write_le(&mut writer)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample random solutions.
        let expected = crate::solutions::serialize::tests::sample_solutions(&mut rng);

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Solutions::read_le(&expected_bytes[..])?);
        Ok(())
    }
}
