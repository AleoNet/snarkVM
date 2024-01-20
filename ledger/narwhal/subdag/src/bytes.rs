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
        // TODO (howardwu): For mainnet - Change the version back to 1.
        if version != 1 && version != 2 {
            return Err(error(format!("Invalid subdag version ({version})")));
        }

        // Read the number of rounds.
        let num_rounds = u32::read_le(&mut reader)?;
        // Ensure the number of rounds is within bounds.
        if num_rounds as usize > Self::MAX_ROUNDS {
            return Err(error(format!("Number of rounds ({num_rounds}) exceeds the maximum ({})", Self::MAX_ROUNDS)));
        }
        // Read the round certificates.
        let mut subdag = BTreeMap::new();
        for _ in 0..num_rounds {
            // Read the round.
            let round = u64::read_le(&mut reader)?;
            // Read the number of certificates.
            let num_certificates = u32::read_le(&mut reader)?;
            // Ensure the number of certificates is within bounds.
            if num_certificates as usize > BatchHeader::<N>::MAX_CERTIFICATES {
                return Err(error(format!(
                    "Number of certificates ({num_certificates}) exceeds the maximum ({})",
                    BatchHeader::<N>::MAX_CERTIFICATES
                )));
            }
            // Read the certificates.
            let mut certificates = IndexSet::new();
            for _ in 0..num_certificates {
                // Read the certificate.
                certificates.insert(BatchCertificate::read_le(&mut reader)?);
            }
            // Insert the round and certificates.
            subdag.insert(round, certificates);
        }

        // Read the election certificate IDs.
        let mut election_certificate_ids = IndexSet::new();
        // TODO (howardwu): For mainnet - Always attempt to deserialize the election certificate IDs.
        if version != 1 {
            // Read the number of election certificate IDs.
            let num_election_certificate_ids = u16::read_le(&mut reader)?;
            // Ensure the number of election certificate IDs is within bounds.
            if num_election_certificate_ids as usize > BatchHeader::<N>::MAX_CERTIFICATES {
                return Err(error(format!(
                    "Number of election certificate IDs ({num_election_certificate_ids}) exceeds the maximum ({})",
                    BatchHeader::<N>::MAX_CERTIFICATES
                )));
            }
            for _ in 0..num_election_certificate_ids {
                // Read the election certificate ID.
                election_certificate_ids.insert(Field::read_le(&mut reader)?);
            }
        }

        // Return the subdag.
        Self::from(subdag, election_certificate_ids).map_err(error)
    }
}

impl<N: Network> ToBytes for Subdag<N> {
    /// Writes the subdag to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        // TODO (howardwu): For mainnet - Change the version back to 1.
        2u8.write_le(&mut writer)?;
        // Write the number of rounds.
        u32::try_from(self.subdag.len()).map_err(error)?.write_le(&mut writer)?;
        // Write the round certificates.
        for (round, certificates) in &self.subdag {
            // Write the round.
            round.write_le(&mut writer)?;
            // Write the number of certificates.
            u32::try_from(certificates.len()).map_err(error)?.write_le(&mut writer)?;
            // Write the certificates.
            for certificate in certificates {
                // Write the certificate.
                certificate.write_le(&mut writer)?;
            }
        }
        // Write the number of election certificate IDs.
        u16::try_from(self.election_certificate_ids.len()).map_err(error)?.write_le(&mut writer)?;
        // Write the election certificate IDs.
        for election_certificate_id in &self.election_certificate_ids {
            // Write the election certificate ID.
            election_certificate_id.write_le(&mut writer)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes() {
        let rng = &mut TestRng::default();

        for expected in crate::test_helpers::sample_subdags(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, Subdag::read_le(&expected_bytes[..]).unwrap());
        }
    }
}
