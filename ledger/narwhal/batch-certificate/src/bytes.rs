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
        if version != 1 && version != 2 {
            return Err(error("Invalid batch certificate version"));
        }

        if version == 1 {
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
            Self::from_v1_deprecated(certificate_id, batch_header, signatures).map_err(error)
        } else if version == 2 {
            // Read the batch header.
            let batch_header = BatchHeader::read_le(&mut reader)?;
            // Read the number of signatures.
            let num_signatures = u16::read_le(&mut reader)?;
            // Read the signatures.
            let mut signatures = IndexSet::with_capacity(num_signatures as usize);
            for _ in 0..num_signatures {
                // Read the signature.
                let signature = Signature::read_le(&mut reader)?;
                // Insert the signature.
                signatures.insert(signature);
            }
            // Return the batch certificate.
            Self::from(batch_header, signatures).map_err(error)
        } else {
            unreachable!("Invalid batch certificate version")
        }
    }
}

impl<N: Network> ToBytes for BatchCertificate<N> {
    /// Writes the batch certificate to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::V1 { certificate_id, batch_header, signatures } => {
                // Write the version.
                1u8.write_le(&mut writer)?;
                // Write the certificate ID.
                certificate_id.write_le(&mut writer)?;
                // Write the batch header.
                batch_header.write_le(&mut writer)?;
                // Write the number of signatures.
                u32::try_from(signatures.len()).map_err(error)?.write_le(&mut writer)?;
                // Write the signatures.
                for (signature, timestamp) in signatures.iter() {
                    // Write the signature.
                    signature.write_le(&mut writer)?;
                    // Write the timestamp.
                    timestamp.write_le(&mut writer)?;
                }
            }
            Self::V2 { batch_header, signatures } => {
                // Write the version.
                2u8.write_le(&mut writer)?;
                // Write the batch header.
                batch_header.write_le(&mut writer)?;
                // Write the number of signatures.
                u16::try_from(signatures.len()).map_err(error)?.write_le(&mut writer)?;
                // Write the signatures.
                for signature in signatures.iter() {
                    // Write the signature.
                    signature.write_le(&mut writer)?;
                }
            }
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

        for expected in crate::test_helpers::sample_batch_certificates(rng) {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            assert_eq!(expected, BatchCertificate::read_le(&expected_bytes[..]).unwrap());
        }
    }
}
