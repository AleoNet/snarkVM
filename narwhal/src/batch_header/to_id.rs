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

impl<N: Network> BatchHeader<N> {
    /// Returns the batch ID.
    pub fn to_id(&self) -> Result<Field<N>> {
        Self::compute_batch_id(self.round, self.timestamp, &self.transmission_ids, &self.previous_certificates)
    }
}

impl<N: Network> BatchHeader<N> {
    /// Returns the batch ID.
    pub fn compute_batch_id(
        round: u64,
        timestamp: i64,
        transmission_ids: &IndexSet<TransmissionID<N>>,
        previous_certificates: &IndexSet<BatchCertificate<N>>,
    ) -> Result<Field<N>> {
        let mut preimage = Vec::new();
        // Insert the round number.
        preimage.extend_from_slice(&round.to_bytes_le()?);
        // Insert the timestamp.
        preimage.extend_from_slice(&timestamp.to_bytes_le()?);
        // Insert the number of transmissions.
        preimage.extend_from_slice(&u64::try_from(transmission_ids.len())?.to_bytes_le()?);
        // Insert the transmission IDs.
        for transmission_id in transmission_ids {
            preimage.extend_from_slice(&transmission_id.to_bytes_le()?);
        }
        // Insert the number of previous certificates.
        preimage.extend_from_slice(&u64::try_from(previous_certificates.len())?.to_bytes_le()?);
        // Insert the previous certificates.
        for certificate in previous_certificates {
            // Insert the batch ID.
            preimage.extend_from_slice(&certificate.batch_id().to_bytes_le()?);
            // Insert the number of signatures.
            preimage.extend_from_slice(&u64::try_from(certificate.signatures().len())?.to_bytes_le()?);
            // Insert the signatures.
            for signature in certificate.signatures() {
                preimage.extend_from_slice(&signature.to_bytes_le()?);
            }
        }
        // Hash the preimage.
        N::hash_bhp1024(&preimage.to_bits_le())
    }
}
