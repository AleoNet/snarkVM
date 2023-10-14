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

use console::{account::Address, prelude::*, program::SUBDAG_CERTIFICATES_DEPTH, types::Field};
use narwhal_batch_certificate::BatchCertificate;
use narwhal_transmission_id::TransmissionID;

use indexmap::IndexSet;
use std::collections::BTreeMap;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

/// Returns `true` if the rounds are sequential.
fn is_sequential<T>(map: &BTreeMap<u64, T>) -> bool {
    let mut previous_round = None;
    for &round in map.keys() {
        match previous_round {
            Some(previous) if previous + 1 != round => return false,
            _ => previous_round = Some(round),
        }
    }
    true
}

/// Returns `true` if the DFS traversal using the given subdag structure matches the commit.
fn sanity_check_subdag_with_dfs<N: Network>(subdag: &BTreeMap<u64, IndexSet<BatchCertificate<N>>>) -> bool {
    use std::collections::HashSet;

    // Initialize a map for the certificates to commit.
    let mut commit = BTreeMap::<u64, IndexSet<_>>::new();
    // Initialize a set for the already ordered certificates.
    let mut already_ordered = HashSet::new();
    // Initialize a buffer for the certificates to order, starting with the leader certificate.
    let mut buffer = subdag.iter().next_back().map_or(Default::default(), |(_, leader)| leader.clone());
    // Iterate over the certificates to order.
    while let Some(certificate) = buffer.pop() {
        // Insert the certificate into the map.
        commit.entry(certificate.round()).or_default().insert(certificate.clone());
        // Iterate over the previous certificate IDs.
        for previous_certificate_id in certificate.previous_certificate_ids() {
            let Some(previous_certificate) = subdag.get(&(certificate.round() - 1)).and_then(|map| {
                map.iter().find(|certificate| certificate.certificate_id() == *previous_certificate_id)
            }) else {
                // It is either ordered or below the GC round.
                continue;
            };
            // Insert the previous certificate into the set of already ordered certificates.
            if !already_ordered.insert(previous_certificate.certificate_id()) {
                // If the previous certificate is already ordered, continue.
                continue;
            }
            // Insert the previous certificate into the buffer.
            buffer.insert(previous_certificate.clone());
        }
    }
    // Return `true` if the subdag matches the commit.
    &commit == subdag
}

#[derive(Clone, PartialEq, Eq)]
pub struct Subdag<N: Network> {
    /// The subdag of round certificates.
    subdag: BTreeMap<u64, IndexSet<BatchCertificate<N>>>,
}

impl<N: Network> Subdag<N> {
    /// Initializes a new subdag.
    pub fn from(subdag: BTreeMap<u64, IndexSet<BatchCertificate<N>>>) -> Result<Self> {
        // Ensure the subdag is not empty.
        ensure!(!subdag.is_empty(), "Subdag cannot be empty");
        // Ensure the anchor round is even.
        ensure!(subdag.iter().next_back().map_or(0, |(r, _)| *r) % 2 == 0, "Anchor round must be even");
        // Ensure there is only one leader certificate.
        ensure!(subdag.iter().next_back().map_or(0, |(_, c)| c.len()) == 1, "Subdag cannot have multiple leaders");
        // Ensure the rounds are sequential.
        ensure!(is_sequential(&subdag), "Subdag rounds must be sequential");
        // Ensure the subdag structure matches the commit.
        ensure!(sanity_check_subdag_with_dfs(&subdag), "Subdag structure does not match commit");
        // Ensure the leader certificate is an even round.
        Ok(Self { subdag })
    }
}

impl<N: Network> Subdag<N> {
    /// Returns the anchor round.
    pub fn anchor_round(&self) -> u64 {
        self.subdag.iter().next_back().map_or(0, |(round, _)| *round)
    }

    /// Returns the certificate IDs of the subdag (from earliest round to latest round).
    pub fn certificate_ids(&self) -> impl Iterator<Item = Field<N>> + '_ {
        self.values().flatten().map(BatchCertificate::certificate_id)
    }

    /// Returns the leader certificate.
    pub fn leader_certificate(&self) -> &BatchCertificate<N> {
        // Retrieve entry for the anchor round.
        let entry = self.subdag.iter().next_back();
        debug_assert!(entry.is_some(), "There must be at least one round of certificates");
        // Retrieve the certificates from the anchor round.
        let certificates = entry.expect("There must be one round in the subdag").1;
        debug_assert!(certificates.len() == 1, "There must be only one leader certificate, by definition");
        // Note: There is guaranteed to be only one leader certificate.
        certificates.iter().next().expect("There must be a leader certificate")
    }

    /// Returns the address of the leader.
    pub fn leader_address(&self) -> Address<N> {
        // Retrieve the leader address from the leader certificate.
        self.leader_certificate().author()
    }

    /// Returns the transmission IDs of the subdag (from earliest round to latest round).
    pub fn transmission_ids(&self) -> impl Iterator<Item = &TransmissionID<N>> {
        self.values().flatten().flat_map(BatchCertificate::transmission_ids)
    }

    /// Returns the timestamp of the anchor round, defined as the median timestamp of the leader certificate.
    pub fn timestamp(&self) -> i64 {
        // Retrieve the median timestamp from the leader certificate.
        self.leader_certificate().median_timestamp()
    }

    /// Returns the subdag root of the transactions.
    pub fn to_subdag_root(&self) -> Result<Field<N>> {
        // Prepare the leaves.
        let leaves = cfg_iter!(self.subdag)
            .map(|(_, certificates)| {
                certificates
                    .iter()
                    .flat_map(|certificate| certificate.certificate_id().to_bits_le())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Compute the subdag tree.
        let tree = N::merkle_tree_bhp::<SUBDAG_CERTIFICATES_DEPTH>(&leaves)?;
        // Return the subdag root.
        Ok(*tree.root())
    }
}

impl<N: Network> Deref for Subdag<N> {
    type Target = BTreeMap<u64, IndexSet<BatchCertificate<N>>>;

    /// Returns the batch certificates.
    fn deref(&self) -> &Self::Target {
        &self.subdag
    }
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::{network::Testnet3, prelude::TestRng};

    use indexmap::{indexset, IndexSet};

    type CurrentNetwork = Testnet3;

    /// Returns a sample subdag, sampled at random.
    pub fn sample_subdag(rng: &mut TestRng) -> Subdag<CurrentNetwork> {
        const F: usize = 1;
        const AVAILABILITY_THRESHOLD: usize = F + 1;
        const QUORUM_THRESHOLD: usize = 2 * F + 1;

        // Initialize the map for the subdag.
        let mut subdag = BTreeMap::<u64, IndexSet<_>>::new();

        // Initialize the starting round.
        let starting_round = {
            loop {
                let round = rng.gen_range(2..u64::MAX);
                if round % 2 == 0 {
                    break round;
                }
            }
        };

        // Process the earliest round.
        let mut previous_certificate_ids = IndexSet::new();
        for _ in 0..AVAILABILITY_THRESHOLD {
            let certificate =
                narwhal_batch_certificate::test_helpers::sample_batch_certificate_for_round(starting_round, rng);
            previous_certificate_ids.insert(certificate.certificate_id());
            subdag.entry(starting_round).or_default().insert(certificate);
        }

        // Process the middle round.
        let mut previous_certificate_ids_2 = IndexSet::new();
        for _ in 0..QUORUM_THRESHOLD {
            let certificate =
                narwhal_batch_certificate::test_helpers::sample_batch_certificate_for_round_with_previous_certificate_ids(starting_round + 1, previous_certificate_ids.clone(), rng);
            previous_certificate_ids_2.insert(certificate.certificate_id());
            subdag.entry(starting_round + 1).or_default().insert(certificate);
        }

        // Process the latest round.
        let certificate =
            narwhal_batch_certificate::test_helpers::sample_batch_certificate_for_round_with_previous_certificate_ids(
                starting_round + 2,
                previous_certificate_ids_2,
                rng,
            );
        subdag.insert(starting_round + 2, indexset![certificate]);

        // Return the subdag.
        Subdag::from(subdag).unwrap()
    }

    /// Returns a list of sample subdags, sampled at random.
    pub fn sample_subdags(rng: &mut TestRng) -> Vec<Subdag<CurrentNetwork>> {
        // Initialize a sample vector.
        let mut sample = Vec::with_capacity(10);
        // Append sample subdags.
        for _ in 0..10 {
            sample.push(sample_subdag(rng));
        }
        // Return the sample vector.
        sample
    }
}
