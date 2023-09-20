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

#![forbid(unsafe_code)]
#![warn(clippy::cast_possible_truncation)]

mod bytes;
mod serialize;
mod string;
mod to_id;

use console::{
    account::{Address, PrivateKey, Signature},
    prelude::*,
    types::Field,
};
use indexmap::{IndexMap, IndexSet};
use narwhal_batch_header::BatchHeader;
use narwhal_transmission_id::{TransmissionID, TransmissionType};

/// Returns `true` if the transmission id indexes are properly formatted.
fn sanity_check_indexes(transmission_ids_map: &IndexSet<(TransmissionType, u32)>) -> bool {
    // Track the indexes for each transmission type.
    let mut indices = IndexMap::new();

    // Ensure that the index increments properly for each transmission type.
    for (transmission_type, index) in transmission_ids_map {
        let current_index = indices.entry(transmission_type).or_insert(0);
        if *index != *current_index {
            return false;
        }
        *current_index = current_index.saturating_add(1);
    }

    true
}

#[derive(Clone, PartialEq, Eq)]
pub struct CompactBatchHeader<N: Network> {
    /// The batch ID, defined as the hash of the round number, timestamp, transmission IDs, and previous batch certificate IDs.
    batch_id: Field<N>,
    /// The author of the batch.
    author: Address<N>,
    /// The round number.
    round: u64,
    /// The timestamp.
    timestamp: i64,
    /// The set of index references for the `transmission IDs`.
    transmission_ids_map: IndexSet<(TransmissionType, u32)>,
    /// The batch certificate IDs of the previous round.
    previous_certificate_ids: IndexSet<Field<N>>,
    /// The signature of the batch ID from the creator.
    signature: Signature<N>,
}

impl<N: Network> CompactBatchHeader<N> {
    /// Initializes a new batch header.
    pub fn new<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        round: u64,
        timestamp: i64,
        transmission_ids: IndexSet<TransmissionID<N>>,
        previous_certificate_ids: IndexSet<Field<N>>,
        rng: &mut R,
    ) -> Result<Self> {
        match round {
            // If the round is zero or one, then there should be no previous certificate IDs.
            0 | 1 => ensure!(previous_certificate_ids.is_empty(), "Invalid round number, must not have certificates"),
            // If the round is not zero and not one, then there should be at least one previous certificate ID.
            _ => ensure!(!previous_certificate_ids.is_empty(), "Invalid round number, must have certificates"),
        }
        // Retrieve the address.
        let author = Address::try_from(private_key)?;
        // Compute the batch ID.
        let batch_id = Self::compute_batch_id(author, round, timestamp, &transmission_ids, &previous_certificate_ids)?;
        // Sign the preimage.
        let signature = private_key.sign(&[batch_id], rng)?;

        // Construct the index references for the transmission IDs.
        let transmission_ids_map = Self::to_map(&transmission_ids);

        // Return the batch header.
        Ok(Self { author, batch_id, round, timestamp, transmission_ids_map, previous_certificate_ids, signature })
    }

    /// Initializes a new batch header.
    pub fn from(
        batch_id: Field<N>,
        author: Address<N>,
        round: u64,
        timestamp: i64,
        transmission_ids_map: IndexSet<(TransmissionType, u32)>,
        previous_certificate_ids: IndexSet<Field<N>>,
        signature: Signature<N>,
    ) -> Result<Self> {
        match round {
            // If the round is zero or one, then there should be no previous certificate IDs.
            0 | 1 => ensure!(previous_certificate_ids.is_empty(), "Invalid round number, must not have certificates"),
            // If the round is not zero and not one, then there should be at least one previous certificate ID.
            _ => ensure!(!previous_certificate_ids.is_empty(), "Invalid round number, must have certificates"),
        }
        // Verify the signature.
        if !signature.verify(&author, &[batch_id]) {
            bail!("Invalid signature for the batch header");
        }
        // Ensure the transmission id indexes are properly constructed.
        ensure!(sanity_check_indexes(&transmission_ids_map), "Transmission id indexes are not properly constructed");

        // Return the batch header.
        Ok(Self { author, batch_id, round, timestamp, transmission_ids_map, previous_certificate_ids, signature })
    }

    /// Initializes a new compact batch header from a batch header.
    pub fn from_batch_header(batch_header: &BatchHeader<N>) -> Result<Self> {
        // Construct the transmission IDs map.
        let transmission_ids_map = Self::to_map(batch_header.transmission_ids());

        // Return the compact batch header.
        Self::from(
            batch_header.batch_id(),
            batch_header.author(),
            batch_header.round(),
            batch_header.timestamp(),
            transmission_ids_map,
            batch_header.previous_certificate_ids().clone(),
            *batch_header.signature(),
        )
    }

    /// Returns the mapped indexes for the given set of transmission ids.
    pub fn to_map(transmission_ids: &IndexSet<TransmissionID<N>>) -> IndexSet<(TransmissionType, u32)> {
        // Construct the transmission IDs map.
        let mut transmission_ids_map = IndexSet::with_capacity(transmission_ids.len());

        // Track the indexes for ratifications, transactions, and solutions.
        let (mut ratifications_index, mut transactions_index, mut solutions_index) = (0u32, 0u32, 0u32);
        for transmission in transmission_ids.iter() {
            match transmission {
                TransmissionID::Ratification => {
                    transmission_ids_map.insert((TransmissionType::Ratification, ratifications_index));
                    ratifications_index += 1;
                }
                TransmissionID::Transaction(_) => {
                    transmission_ids_map.insert((TransmissionType::Transaction, transactions_index));
                    transactions_index += 1;
                }
                TransmissionID::Solution(_) => {
                    transmission_ids_map.insert((TransmissionType::Solution, solutions_index));
                    solutions_index += 1;
                }
            }
        }

        transmission_ids_map
    }
}

impl<N: Network> CompactBatchHeader<N> {
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

    /// Returns the indexes for the transmission IDs.
    pub const fn transmission_ids_map(&self) -> &IndexSet<(TransmissionType, u32)> {
        &self.transmission_ids_map
    }

    /// Returns the batch certificate IDs for the previous round.
    pub const fn previous_certificate_ids(&self) -> &IndexSet<Field<N>> {
        &self.previous_certificate_ids
    }

    /// Returns the signature.
    pub const fn signature(&self) -> &Signature<N> {
        &self.signature
    }
}

impl<N: Network> CompactBatchHeader<N> {
    /// Returns `true` if the batch header is empty.
    pub fn is_empty(&self) -> bool {
        self.transmission_ids_map.is_empty()
    }

    /// Returns the number of transmissions in the batch header.
    pub fn len(&self) -> usize {
        self.transmission_ids_map.len()
    }
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::{account::PrivateKey, network::Testnet3, prelude::TestRng};

    use time::OffsetDateTime;

    type CurrentNetwork = Testnet3;

    /// Returns a sample compact batch header, sampled at random.
    pub fn sample_compact_batch_header(rng: &mut TestRng) -> CompactBatchHeader<CurrentNetwork> {
        sample_compact_batch_header_for_round(rng.gen(), rng)
    }

    /// Returns a sample batch header with a given round; the rest is sampled at random.
    pub fn sample_compact_batch_header_for_round(round: u64, rng: &mut TestRng) -> CompactBatchHeader<CurrentNetwork> {
        // Sample certificate IDs.
        let certificate_ids = (0..10).map(|_| Field::<CurrentNetwork>::rand(rng)).collect::<IndexSet<_>>();
        // Return the compact batch header.
        sample_compact_batch_header_for_round_with_previous_certificate_ids(round, certificate_ids, rng)
    }

    /// Returns a sample batch header with a given round and set of previous certificate IDs; the rest is sampled at random.
    pub fn sample_compact_batch_header_for_round_with_previous_certificate_ids(
        round: u64,
        previous_certificate_ids: IndexSet<Field<CurrentNetwork>>,
        rng: &mut TestRng,
    ) -> CompactBatchHeader<CurrentNetwork> {
        // Sample a private key.
        let private_key = PrivateKey::new(rng).unwrap();
        // Sample transmission IDs.
        let transmission_ids =
            narwhal_transmission_id::test_helpers::sample_transmission_ids(rng).into_iter().collect::<IndexSet<_>>();
        // Checkpoint the timestamp for the batch.
        let timestamp = OffsetDateTime::now_utc().unix_timestamp();
        // Return the compact batch header.
        CompactBatchHeader::new(&private_key, round, timestamp, transmission_ids, previous_certificate_ids, rng)
            .unwrap()
    }

    /// Returns a list of sample compact batch headers, sampled at random.
    pub fn sample_compact_batch_headers(rng: &mut TestRng) -> Vec<CompactBatchHeader<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = Vec::with_capacity(10);
        // Append sample batches.
        for _ in 0..10 {
            // Append the batch header.
            sample.push(sample_compact_batch_header(rng));
        }
        // Return the sample vector.
        sample
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_from_batch_header() {
        let rng = &mut TestRng::default();

        // Sample batch headers
        let batch_headers = narwhal_batch_header::test_helpers::sample_batch_headers(rng);

        for batch_header in batch_headers {
            // Convert the batch header to a compact batch header.
            let compact_batch_header = CompactBatchHeader::from_batch_header(&batch_header).unwrap();

            // Check that the transmission IDs map is correct.
            let expected_transmission_ids_map = CompactBatchHeader::to_map(batch_header.transmission_ids());
            assert_eq!(compact_batch_header.transmission_ids_map(), &expected_transmission_ids_map);

            // Check that the rest of the fields are correct.
            assert_eq!(compact_batch_header.batch_id(), batch_header.batch_id());
            assert_eq!(compact_batch_header.author(), batch_header.author());
            assert_eq!(compact_batch_header.round(), batch_header.round());
            assert_eq!(compact_batch_header.timestamp(), batch_header.timestamp());
            assert_eq!(compact_batch_header.previous_certificate_ids(), batch_header.previous_certificate_ids());
            assert_eq!(compact_batch_header.signature(), batch_header.signature());
        }
    }
}
