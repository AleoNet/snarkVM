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

mod bytes;
mod serialize;
mod to_header;

use crate::{BatchCertificate, BatchHeader, Transmission, TransmissionID};
use console::{
    account::{Address, PrivateKey, Signature},
    prelude::*,
    types::Field,
};

use indexmap::{IndexMap, IndexSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Batch<N: Network> {
    /// The batch ID, defined as the hash of the round number, timestamp, transmission IDs, and previous batch certificates.
    batch_id: Field<N>,
    /// The author of the batch.
    author: Address<N>,
    /// The round number.
    round: u64,
    /// The timestamp.
    timestamp: i64,
    /// The map of `transmission IDs` to `transmissions`.
    transmissions: IndexMap<TransmissionID<N>, Transmission<N>>,
    /// The batch certificates of the previous round.
    previous_certificates: IndexSet<BatchCertificate<N>>,
    /// The signature of the batch ID from the creator.
    signature: Signature<N>,
}

impl<N: Network> Batch<N> {
    /// Initializes a new batch.
    pub fn new<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        round: u64,
        timestamp: i64,
        transmissions: IndexMap<TransmissionID<N>, Transmission<N>>,
        previous_certificates: IndexSet<BatchCertificate<N>>,
        rng: &mut R,
    ) -> Result<Self> {
        match round {
            // If the round is zero or one, then there should be no previous certificates.
            0 | 1 => ensure!(previous_certificates.is_empty(), "Invalid round number, must not have certificates"),
            // If the round is not zero and not one, then there should be at least one previous certificate.
            _ => ensure!(!previous_certificates.is_empty(), "Invalid round number, must have certificates"),
        }
        // Ensure there are transmissions in the batch.
        ensure!(!transmissions.is_empty(), "Batch must contain at least one transmission");
        // Construct the author.
        let author = Address::try_from(private_key)?;
        // Construct the transmission IDs.
        let transmission_ids = transmissions.keys().copied().collect();
        // Compute the previous certificate IDs.
        let previous_certificate_ids = previous_certificates.iter().map(|c| c.certificate_id()).collect();
        // Compute the batch ID.
        let batch_id =
            BatchHeader::compute_batch_id(author, round, timestamp, &transmission_ids, &previous_certificate_ids)?;
        // Sign the preimage.
        let signature = private_key.sign(&[batch_id, Field::from_u64(timestamp as u64)], rng)?;
        // Return the batch.
        Ok(Self { author, batch_id, round, timestamp, transmissions, previous_certificates, signature })
    }

    /// Initializes a new batch.
    pub fn from(
        author: Address<N>,
        round: u64,
        timestamp: i64,
        transmissions: IndexMap<TransmissionID<N>, Transmission<N>>,
        previous_certificates: IndexSet<BatchCertificate<N>>,
        signature: Signature<N>,
    ) -> Result<Self> {
        match round {
            // If the round is zero or one, then there should be no previous certificates.
            0 | 1 => ensure!(previous_certificates.is_empty(), "Invalid round number, must not have certificates"),
            // If the round is not zero and not one, then there should be at least one previous certificate.
            _ => ensure!(!previous_certificates.is_empty(), "Invalid round number, must have certificates"),
        }
        // Ensure there are transmissions in the batch.
        ensure!(!transmissions.is_empty(), "Batch must contain at least one transmission");
        // Construct the transmission IDs.
        let transmission_ids = transmissions.keys().copied().collect();
        // Compute the previous certificate IDs.
        let previous_certificate_ids = previous_certificates.iter().map(|c| c.certificate_id()).collect();
        // Compute the batch ID.
        let batch_id =
            BatchHeader::compute_batch_id(author, round, timestamp, &transmission_ids, &previous_certificate_ids)?;
        // Verify the signature.
        if !signature.verify(&author, &[batch_id, Field::from_u64(timestamp as u64)]) {
            bail!("Invalid signature for the batch");
        }
        // Return the batch.
        Ok(Self { author, batch_id, round, timestamp, transmissions, previous_certificates, signature })
    }
}

impl<N: Network> Batch<N> {
    /// Returns the batch ID.
    pub const fn batch_id(&self) -> Field<N> {
        self.batch_id
    }

    /// Returns the author.
    pub const fn author(&self) -> Address<N> {
        self.author
    }

    /// Returns the round number.
    pub const fn round(&self) -> u64 {
        self.round
    }

    /// Returns the timestamp.
    pub const fn timestamp(&self) -> i64 {
        self.timestamp
    }

    /// Returns the transmission IDs.
    pub fn transmission_ids(&self) -> IndexSet<TransmissionID<N>> {
        self.transmissions.keys().copied().collect()
    }

    /// Returns the transmissions.
    pub const fn transmissions(&self) -> &IndexMap<TransmissionID<N>, Transmission<N>> {
        &self.transmissions
    }

    /// Returns the transmissions.
    pub fn into_transmissions(self) -> IndexMap<TransmissionID<N>, Transmission<N>> {
        self.transmissions
    }

    /// Returns the batch certificates for the previous round.
    pub const fn previous_certificates(&self) -> &IndexSet<BatchCertificate<N>> {
        &self.previous_certificates
    }

    /// Returns the signature.
    pub const fn signature(&self) -> &Signature<N> {
        &self.signature
    }
}

impl<N: Network> Batch<N> {
    /// Returns `true` if the batch is empty.
    pub fn is_empty(&self) -> bool {
        self.transmissions.is_empty()
    }

    /// Returns the number of transmissions in the batch.
    pub fn len(&self) -> usize {
        self.transmissions.len()
    }

    /// Returns `true` if the batch contains the specified `transmission ID`.
    pub fn contains(&self, transmission_id: impl Into<TransmissionID<N>>) -> bool {
        self.transmissions.contains_key(&transmission_id.into())
    }

    /// Returns the transmission, given the specified `transmission ID`.
    pub fn get(&self, transmission_id: impl Into<TransmissionID<N>>) -> Option<&Transmission<N>> {
        self.transmissions.get(&transmission_id.into())
    }
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3, prelude::TestRng};
    use time::OffsetDateTime;

    type CurrentNetwork = Testnet3;

    /// Returns a list of sample batches, sampled at random.
    pub fn sample_batches(rng: &mut TestRng) -> Vec<Batch<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = Vec::with_capacity(10);
        // Append sample batches.
        for _ in 0..10 {
            // Sample a private key.
            let private_key = PrivateKey::new(rng).unwrap();
            // Sample transmission IDs.
            let transmission_ids = crate::transmission_id::test_helpers::sample_transmission_ids(rng);
            // Sample transmissions.
            let transmissions = crate::transmission::test_helpers::sample_transmissions(rng);
            // Combine the transmission IDs and transmissions.
            let transmissions = transmission_ids.into_iter().zip(transmissions.into_iter()).collect::<IndexMap<_, _>>();
            assert!(!transmissions.is_empty());
            // Sample certificates.
            let certificates = crate::batch_certificate::test_helpers::sample_batch_certificates(rng);
            // Checkpoint the timestamp for the batch.
            let timestamp = OffsetDateTime::now_utc().unix_timestamp();
            // Append the batch.
            sample.push(Batch::new(&private_key, rng.gen(), timestamp, transmissions, certificates, rng).unwrap());
        }
        // Return the sample vector.
        sample
    }
}
