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

impl<N: Network> FromBytes for Batch<N> {
    /// Reads the batch from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid batch version"));
        }

        // Read the batch ID.
        let batch_id = Field::read_le(&mut reader)?;
        // Read the round number.
        let round = u64::read_le(&mut reader)?;
        // Read the timestamp.
        let timestamp = i64::read_le(&mut reader)?;

        // Read the number of transmissions.
        let num_transmissions = u32::read_le(&mut reader)?;
        // Read the transmissions.
        let mut transmissions = HashMap::new();
        for _ in 0..num_transmissions {
            // Read the transmission ID.
            let transmission_id = TransmissionID::read_le(&mut reader)?;
            // Read the transmission.
            let transmission = Transmission::read_le(&mut reader)?;
            // Insert the transmission.
            transmissions.insert(transmission_id, transmission);
        }

        // Read the number of previous certificates.
        let num_previous_certificates = u32::read_le(&mut reader)?;
        // Read the previous certificates.
        let mut previous_certificates = Vec::new();
        for _ in 0..num_previous_certificates {
            // Read the certificate.
            previous_certificates.push(BatchCertificate::read_le(&mut reader)?);
        }

        // Read the signature.
        let signature = Signature::read_le(&mut reader)?;

        // Return the batch.
        Ok(Self { batch_id, round, timestamp, transmissions, previous_certificates, signature })
    }
}

impl<N: Network> ToBytes for Batch<N> {
    /// Writes the batch to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;
        // Write the batch ID.
        self.batch_id.write_le(&mut writer)?;
        // Write the round number.
        self.round.write_le(&mut writer)?;
        // Write the timestamp.
        self.timestamp.write_le(&mut writer)?;
        // Write the number of transmissions.
        u32::try_from(self.transmissions.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the transmissions.
        for (transmission_id, transmission) in &self.transmissions {
            // Write the transmission ID.
            transmission_id.write_le(&mut writer)?;
            // Write the transmission.
            transmission.write_le(&mut writer)?;
        }
        // Write the number of previous certificates.
        u32::try_from(self.previous_certificates.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the previous certificates.
        for certificate in &self.previous_certificates {
            // Write the certificate.
            certificate.write_le(&mut writer)?;
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

        for expected in crate::batch::test_helpers::sample_batches(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, Batch::read_le(&expected_bytes[..]).unwrap());
            assert!(Batch::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
