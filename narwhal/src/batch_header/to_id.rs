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
        Self::compute_batch_id(self.round, self.timestamp, &self.transmission_ids, &self.previous_certificate_ids)
    }
}

impl<N: Network> BatchHeader<N> {
    /// Returns the batch ID.
    pub fn compute_batch_id(
        round: u64,
        timestamp: i64,
        transmission_ids: &IndexSet<TransmissionID<N>>,
        previous_certificate_ids: &IndexSet<Field<N>>,
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
        // Insert the number of previous certificate IDs.
        preimage.extend_from_slice(&u64::try_from(previous_certificate_ids.len())?.to_bytes_le()?);
        // Insert the previous certificate IDs.
        for certificate_id in previous_certificate_ids {
            // Insert the certificate ID.
            preimage.extend_from_slice(&certificate_id.to_bytes_le()?);
        }
        // Hash the preimage.
        N::hash_bhp1024(&preimage.to_bits_le())
    }
}
