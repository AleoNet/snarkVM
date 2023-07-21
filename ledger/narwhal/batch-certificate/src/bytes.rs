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

impl<N: Network> FromBytes for BatchCertificate<N> {
    /// Reads the batch certificate from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid batch version"));
        }

        // Read the certificate ID.
        let certificate_id = Field::read_le(&mut reader)?;
        // Read the batch header.
        let batch_header = BatchHeader::read_le(&mut reader)?;
        // Read the number of signatures.
        let num_signatures = u32::read_le(&mut reader)?;
        // Read the signatures.
        let mut signatures = IndexMap::with_capacity(num_signatures as usize);
        for _ in 0..num_signatures {
            // Read the signature.
            let signature = Signature::read_le(&mut reader)?;
            // Read the timestamp.
            let timestamp = i64::read_le(&mut reader)?;
            // Insert the signature and timestamp.
            signatures.insert(signature, timestamp);
        }
        // Return the batch certificate.
        Self::from(certificate_id, batch_header, signatures).map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for BatchCertificate<N> {
    /// Writes the batch certificate to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;
        // Write the certificate ID.
        self.certificate_id.write_le(&mut writer)?;
        // Write the batch header.
        self.batch_header.write_le(&mut writer)?;
        // Write the number of signatures.
        u32::try_from(self.signatures.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the signatures.
        for (signature, timestamp) in &self.signatures {
            // Write the signature.
            signature.write_le(&mut writer)?;
            // Write the timestamp.
            timestamp.write_le(&mut writer)?;
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

        for expected in crate::test_helpers::sample_batch_certificates(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, BatchCertificate::read_le(&expected_bytes[..]).unwrap());
            assert!(BatchCertificate::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
