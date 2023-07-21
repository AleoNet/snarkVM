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

impl<N: Network> FromBytes for BatchHeader<N> {
    /// Reads the batch header from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid batch header version"));
        }

        // Read the batch ID.
        let batch_id = Field::read_le(&mut reader)?;
        // Read the author.
        let author = Address::read_le(&mut reader)?;
        // Read the round number.
        let round = u64::read_le(&mut reader)?;
        // Read the timestamp.
        let timestamp = i64::read_le(&mut reader)?;

        // Read the number of transmission IDs.
        let num_transmissions = u32::read_le(&mut reader)?;
        // Read the transmission IDs.
        let mut transmission_ids = IndexSet::new();
        for _ in 0..num_transmissions {
            // Insert the transmission ID.
            transmission_ids.insert(TransmissionID::read_le(&mut reader)?);
        }

        // Read the number of previous certificate IDs.
        let num_previous_certificate_ids = u32::read_le(&mut reader)?;
        // Read the previous certificate IDs.
        let mut previous_certificate_ids = IndexSet::with_capacity(num_previous_certificate_ids as usize);
        for _ in 0..num_previous_certificate_ids {
            // Read the certificate ID.
            previous_certificate_ids.insert(Field::read_le(&mut reader)?);
        }

        // Read the signature.
        let signature = Signature::read_le(&mut reader)?;

        // Construct the batch.
        let batch = Self::from(author, round, timestamp, transmission_ids, previous_certificate_ids, signature)
            .map_err(|e| error(e.to_string()))?;

        // Return the batch.
        match batch.batch_id == batch_id {
            true => Ok(batch),
            false => Err(error("Invalid batch ID")),
        }
    }
}

impl<N: Network> ToBytes for BatchHeader<N> {
    /// Writes the batch header to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;
        // Write the batch ID.
        self.batch_id.write_le(&mut writer)?;
        // Write the author.
        self.author.write_le(&mut writer)?;
        // Write the round number.
        self.round.write_le(&mut writer)?;
        // Write the timestamp.
        self.timestamp.write_le(&mut writer)?;
        // Write the number of transmission IDs.
        u32::try_from(self.transmission_ids.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the transmission IDs.
        for transmission_id in &self.transmission_ids {
            // Write the transmission ID.
            transmission_id.write_le(&mut writer)?;
        }
        // Write the number of previous certificate IDs.
        u32::try_from(self.previous_certificate_ids.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the previous certificate IDs.
        for certificate_id in &self.previous_certificate_ids {
            // Write the certificate ID.
            certificate_id.write_le(&mut writer)?;
        }
        // Write the signature.
        self.signature.write_le(&mut writer)
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

        for expected in crate::test_helpers::sample_batch_headers(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, BatchHeader::read_le(&expected_bytes[..]).unwrap());
            assert!(BatchHeader::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
