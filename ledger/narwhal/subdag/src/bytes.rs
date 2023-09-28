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

impl<N: Network> FromBytes for Subdag<N> {
    /// Reads the subdag from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 1 {
            return Err(error("Invalid batch version"));
        }

        // Read the number of rounds.
        let num_rounds = u32::read_le(&mut reader)?;
        // Read the round certificates.
        let mut subdag = BTreeMap::new();
        for _ in 0..num_rounds {
            // Read the round.
            let round = u64::read_le(&mut reader)?;
            // Read the number of certificates.
            let num_certificates = u32::read_le(&mut reader)?;
            // Read the certificates.
            let mut certificates = IndexSet::with_capacity(num_certificates as usize);
            for _ in 0..num_certificates {
                // Read the certificate.
                certificates.insert(BatchCertificate::read_le(&mut reader)?);
            }
            // Insert the round and certificates.
            subdag.insert(round, certificates);
        }
        // Return the subdag.
        Self::from(subdag).map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for Subdag<N> {
    /// Writes the subdag to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        1u8.write_le(&mut writer)?;
        // Write the number of rounds.
        u32::try_from(self.subdag.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the round certificates.
        for (round, certificates) in &self.subdag {
            // Write the round.
            round.write_le(&mut writer)?;
            // Write the number of certificates.
            u32::try_from(certificates.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
            // Write the certificates.
            for certificate in certificates {
                // Write the certificate.
                certificate.write_le(&mut writer)?;
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
    fn test_bytes() {
        let rng = &mut TestRng::default();

        for expected in crate::test_helpers::sample_subdags(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, Subdag::read_le(&expected_bytes[..]).unwrap());
            assert!(Subdag::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
