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
use ledger_coinbase::{CoinbaseSolution, PuzzleCommitment};
use narwhal_batch_certificate::BatchCertificate;
use narwhal_batch_header::BatchHeader;
use narwhal_compact_certificate::CompactCertificate;
use narwhal_traits::NarwhalCertificate;

use bit_set::BitSet;
use indexmap::IndexSet;
use std::collections::BTreeMap;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

/// Helper enum to wrap the leader certificate.
enum LeaderCertificate<'a, N: Network> {
    Full(&'a BatchCertificate<N>),
    Compact(&'a CompactCertificate<N>),
}

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
fn sanity_check_subdag_with_dfs<N: Network, C: NarwhalCertificate<N>>(subdag: &BTreeMap<u64, IndexSet<C>>) -> bool {
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
            let Some(previous_certificate) = subdag
                .get(&(certificate.round() - 1))
                .and_then(|map| map.iter().find(|certificate| certificate.id() == *previous_certificate_id))
            else {
                // It is either ordered or below the GC round.
                continue;
            };
            // Insert the previous certificate into the set of already ordered certificates.
            if !already_ordered.insert(previous_certificate.id()) {
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

#[derive(Clone)]
pub enum Subdag<N: Network> {
    Full {
        /// The subdag of round certificates.
        subdag: BTreeMap<u64, IndexSet<BatchCertificate<N>>>,
        /// The election certificate IDs.
        election_certificate_ids: IndexSet<Field<N>>,
    },
    Compact {
        /// The subdag of round certificates.
        subdag: BTreeMap<u64, IndexSet<CompactCertificate<N>>>,
        /// The election certificate IDs.
        election_certificate_ids: IndexSet<Field<N>>,
    },
}

impl<N: Network> PartialEq for Subdag<N> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // Note: We do not check equality on `election_certificate_ids` as it would cause `Block::eq` to trigger false-positives.
            (Self::Full { subdag, .. }, Self::Full { subdag: other_subdag, .. }) => subdag == other_subdag,
            (Self::Compact { subdag, .. }, Self::Compact { subdag: other_subdag, .. }) => subdag == other_subdag,
            _ => false,
        }
    }
}

impl<N: Network> Eq for Subdag<N> {}

impl<N: Network> Subdag<N> {
    /// Initializes a new subdag.
    pub fn from_full(
        subdag: BTreeMap<u64, IndexSet<BatchCertificate<N>>>,
        election_certificate_ids: IndexSet<Field<N>>,
    ) -> Result<Self> {
        // Perform sanity checks.
        Self::sanity_check_subdag(&subdag, &election_certificate_ids)?;
        // Construct the subdag.
        Ok(Self::Full { subdag, election_certificate_ids })
    }

    /// Initializes a new subdag.
    pub fn from_compact(
        subdag: BTreeMap<u64, IndexSet<CompactCertificate<N>>>,
        election_certificate_ids: IndexSet<Field<N>>,
    ) -> Result<Self> {
        // Perform sanity checks.
        Self::sanity_check_subdag(&subdag, &election_certificate_ids)?;
        // Construct the subdag.
        Ok(Self::Compact { subdag, election_certificate_ids })
    }

    /// Performs sanity checks on the subdag
    fn sanity_check_subdag<C: NarwhalCertificate<N>>(
        subdag: &BTreeMap<u64, IndexSet<C>>,
        election_certificate_ids: &IndexSet<Field<N>>,
    ) -> Result<()> {
        // Ensure the subdag is not empty.
        ensure!(!subdag.is_empty(), "Subdag cannot be empty");
        // Ensure the subdag does not exceed the maximum number of rounds.
        ensure!(subdag.len() <= Self::MAX_ROUNDS, "Subdag cannot exceed the maximum number of rounds");
        // Ensure the anchor round is even.
        ensure!(subdag.iter().next_back().map_or(0, |(r, _)| *r) % 2 == 0, "Anchor round must be even");
        // Ensure there is only one leader certificate.
        ensure!(subdag.iter().next_back().map_or(0, |(_, c)| c.len()) == 1, "Subdag cannot have multiple leaders");
        // Ensure the number of election certificate IDs is within bounds.
        ensure!(
            election_certificate_ids.len() <= BatchHeader::<N>::MAX_CERTIFICATES,
            "Number of election certificate IDs exceeds the maximum"
        );
        // Ensure the rounds are sequential.
        ensure!(is_sequential(subdag), "Subdag rounds must be sequential");
        // Ensure the subdag structure matches the commit.
        ensure!(sanity_check_subdag_with_dfs(subdag), "Subdag structure does not match commit");
        Ok(())
    }
}

impl<N: Network> Subdag<N> {
    /// The maximum number of rounds in a subdag (bounded up to GC depth).
    pub const MAX_ROUNDS: usize = 50;
}

impl<N: Network> Subdag<N> {
    /// Returns the anchor round.
    pub fn anchor_round(&self) -> u64 {
        match self {
            Self::Full { subdag, .. } => subdag.iter().next_back().map_or(0, |(round, _)| *round),
            Self::Compact { subdag, .. } => subdag.iter().next_back().map_or(0, |(round, _)| *round),
        }
    }

    /// Returns the certificate IDs of the subdag (from earliest round to latest round).
    pub fn certificate_ids(&self) -> Vec<Field<N>> {
        match self {
            Self::Full { subdag, .. } => subdag.values().flatten().map(BatchCertificate::id).collect_vec(),
            Self::Compact { subdag, .. } => subdag.values().flatten().map(CompactCertificate::id).collect_vec(),
        }
    }

    /// Returns the certificates of the subdag (from earliest round to latest round).
    pub fn into_iter_batch_certificates(self) -> Result<impl Iterator<Item = BatchCertificate<N>>> {
        let Self::Full { subdag, .. } = self else {
            bail!("Can only iter over certificates of Full Subdag.");
        };
        Ok(subdag.into_values().flatten())
    }

    /// Returns the certificate IDs and rounds of the subdag (from earliest round to latest round).
    pub fn certificate_ids_rounds(&self) -> Vec<(Field<N>, u64)> {
        match self {
            Self::Full { subdag, .. } => subdag
                .iter()
                .flat_map(|(round, certificates)| certificates.iter().map(|c| (c.id(), *round)))
                .collect_vec(),
            Self::Compact { subdag, .. } => subdag
                .iter()
                .flat_map(|(round, certificates)| certificates.iter().map(|c| (c.id(), *round)))
                .collect_vec(),
        }
    }

    /// Returns the number of certificates and rounds of the subdag (from earliest round to latest round).
    pub fn num_certificates_rounds(&self) -> Vec<(usize, u64)> {
        match self {
            Self::Full { subdag, .. } => {
                subdag.iter().map(|(round, certificates)| (certificates.len(), *round)).collect_vec()
            }
            Self::Compact { subdag, .. } => {
                subdag.iter().map(|(round, certificates)| (certificates.len(), *round)).collect_vec()
            }
        }
    }

    /// Returns the leader certificate.
    fn leader_certificate(&self) -> LeaderCertificate<N> {
        match self {
            Self::Full { subdag, .. } => {
                // Retrieve entry for the anchor round.
                let entry = subdag.iter().next_back();
                debug_assert!(entry.is_some(), "There must be at least one round of certificates");
                // Retrieve the certificates from the anchor round.
                let certificates = entry.expect("There must be one round in the subdag").1;
                debug_assert!(certificates.len() == 1, "There must be only one leader certificate, by definition");
                // Note: There is guaranteed to be only one leader certificate.
                let cert = certificates.iter().next().expect("There must be a leader certificate");
                LeaderCertificate::Full(cert)
            }
            Self::Compact { subdag, .. } => {
                // Retrieve entry for the anchor round.
                let entry = subdag.iter().next_back();
                debug_assert!(entry.is_some(), "There must be at least one round of certificates");
                // Retrieve the certificates from the anchor round.
                let certificates = entry.expect("There must be one round in the subdag").1;
                debug_assert!(certificates.len() == 1, "There must be only one leader certificate, by definition");
                // Note: There is guaranteed to be only one leader certificate.
                let cert = certificates.iter().next().expect("There must be a leader certificate");
                LeaderCertificate::Compact(cert)
            }
        }
    }

    /// Returns the leader certificate.
    pub fn leader_batch_certificate(&self) -> Result<&BatchCertificate<N>> {
        match self.leader_certificate() {
            LeaderCertificate::Full(cert) => Ok(cert),
            LeaderCertificate::Compact(_) => {
                bail!("We can only return the leader batch certificate of a full Subdag")
            }
        }
    }

    /// Returns the timestamp of the leader certificate.
    pub fn leader_timestamp(&self) -> Result<i64> {
        match self.leader_certificate() {
            LeaderCertificate::Full(cert) => Ok(cert.timestamp()),
            LeaderCertificate::Compact(cert) => Ok(cert.timestamp()),
        }
    }

    /// Return the number of certificates
    pub fn num_certificates(&self) -> usize {
        match self {
            Self::Full { subdag, .. } => subdag.values().flatten().count(),
            Self::Compact { subdag, .. } => subdag.values().flatten().count(),
        }
    }

    /// Return CompactCertificate for a given round
    pub fn get_certificate_for_round(&self, round: u64, certificate_id: &Field<N>) -> Option<&CompactCertificate<N>> {
        let Self::Compact { subdag, .. } = self else {
            return None;
        };
        match subdag.get(&round) {
            Some(certificates) => {
                // Retrieve the certificate for the given certificate ID.
                match certificates.iter().find(|certificate| certificate.id() == *certificate_id) {
                    Some(certificate) => Some(certificate),
                    None => None,
                }
            }
            None => None,
        }
    }

    /// Returns the address of the leader.
    pub fn leader_address(&self) -> Address<N> {
        // Retrieve the leader address from the leader certificate.
        match self.leader_certificate() {
            LeaderCertificate::Full(cert) => cert.author(),
            LeaderCertificate::Compact(cert) => cert.author(),
        }
    }

    /// Returns unique transaction indices of the subdag (from earliest round to latest round).
    pub fn transaction_indices(&self, expected_len: usize) -> Result<BitSet> {
        let Self::Compact { subdag, .. } = self else {
            bail!("A Full Subdag does not have transaction indices.");
        };
        Ok(subdag.values().flatten().map(CompactCertificate::transaction_indices).fold(
            BitSet::with_capacity(expected_len),
            |mut acc, x| {
                acc.union_with(x);
                acc
            },
        ))
    }

    /// Returns unique solution indices of the subdag (from earliest round to latest round).
    pub fn solution_indices(&self, expected_len: usize) -> Result<BitSet> {
        let Self::Compact { subdag, .. } = self else {
            bail!("A Full Subdag does not have solution indices.");
        };
        Ok(subdag.values().flatten().map(CompactCertificate::solution_indices).fold(
            BitSet::with_capacity(expected_len),
            |mut acc, x| {
                acc.union_with(x);
                acc
            },
        ))
    }

    /// Returns the timestamp of the anchor round, defined as the median timestamp of the subdag.
    pub fn timestamp(&self) -> i64 {
        let mut timestamps = match self {
            Self::Compact { subdag, .. } => {
                subdag.values().flatten().map(CompactCertificate::timestamp).collect::<Vec<_>>()
            }
            Self::Full { subdag, .. } => subdag.values().flatten().map(BatchCertificate::timestamp).collect::<Vec<_>>(),
        };
        // Sort the timestamps.
        #[cfg(not(feature = "serial"))]
        timestamps.par_sort_unstable();
        #[cfg(feature = "serial")]
        timestamps.sort_unstable();
        // Return the median timestamp.
        timestamps[timestamps.len() / 2]
    }

    /// Returns the election certificate IDs.
    pub fn election_certificate_ids(&self) -> &IndexSet<Field<N>> {
        match self {
            Self::Full { election_certificate_ids, .. } => election_certificate_ids,
            Self::Compact { election_certificate_ids, .. } => election_certificate_ids,
        }
    }

    /// Returns the subdag root of the transactions.
    pub fn to_subdag_root(&self) -> Result<Field<N>> {
        // Prepare the leaves.
        let leaves = match self {
            Self::Full { subdag, .. } => cfg_iter!(subdag)
                .map(|(_, certificates)| {
                    certificates.iter().flat_map(|certificate| certificate.id().to_bits_le()).collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
            Self::Compact { subdag, .. } => cfg_iter!(subdag)
                .map(|(_, certificates)| {
                    certificates.iter().flat_map(|certificate| certificate.id().to_bits_le()).collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        };
        // Compute the subdag tree.
        let tree = N::merkle_tree_bhp::<SUBDAG_CERTIFICATES_DEPTH>(&leaves)?;
        // Return the subdag root.
        Ok(*tree.root())
    }

    /// Returns the subdag with compact certificates
    pub fn into_compact(
        self,
        ratifications: Vec<N::RatificationID>,
        solutions: Option<&CoinbaseSolution<N>>,
        prior_solutions: Vec<PuzzleCommitment<N>>,
        transaction_ids: Vec<N::TransactionID>,
        prior_transaction_ids: Vec<N::TransactionID>,
        aborted_transaction_ids: Vec<N::TransactionID>,
    ) -> Result<Subdag<N>> {
        let Self::Full { subdag, election_certificate_ids } = self else {
            bail!("Can only turn a Full subdag into a Compact one.")
        };

        // Initialize the new subdag.
        let mut compact_subdag = BTreeMap::new();

        // Iterate over the subdag.
        for (round, batch_certificates) in subdag.into_iter() {
            let certificates = cfg_into_iter!(batch_certificates)
                .map(|batch_certificate| {
                    let ratifications_iter = ratifications.iter();
                    let solutions_iter = solutions.map(|s| s.puzzle_commitments());
                    let prior_solutions_iter = prior_solutions.iter();
                    let transactions_iter = transaction_ids.iter();
                    let prior_transactions_iter = prior_transaction_ids.iter();
                    let aborted_tx_iter = aborted_transaction_ids.iter();
                    CompactCertificate::from_batch_certificate(
                        batch_certificate,
                        ratifications_iter,
                        solutions_iter,
                        prior_solutions_iter,
                        transactions_iter,
                        prior_transactions_iter,
                        aborted_tx_iter,
                    )
                })
                .collect::<Result<_>>()?;
            compact_subdag.insert(round, certificates);
        }

        // Return the compact certificates.
        Ok(Self::Compact { subdag: compact_subdag, election_certificate_ids })
    }

    /// Returns the subdag with full batch certificates.
    pub fn into_full(
        self,
        ratifications: Vec<N::RatificationID>,
        solutions: Option<CoinbaseSolution<N>>,
        prior_solutions: Vec<PuzzleCommitment<N>>,
        transaction_ids: Vec<N::TransactionID>,
        prior_transactions: Vec<N::TransactionID>,
        aborted_transaction_ids: Vec<N::TransactionID>,
    ) -> Result<Subdag<N>> {
        let Self::Compact { subdag, election_certificate_ids } = self else {
            bail!("Can only turn a Compact subdag into a Full one.")
        };
        // Initialize the new subdag.
        let mut batch_subdag = BTreeMap::new();

        // Iterate over the subdag.
        for (round, compact_certificates) in subdag.into_iter() {
            let mut batch_certificates = IndexSet::with_capacity(compact_certificates.len());
            for certificate in compact_certificates.into_iter() {
                // Create iters.
                let ratifications_iter = ratifications.iter();
                let solutions_iter = solutions.as_ref().map(|s| s.puzzle_commitments());
                let prior_solutions_iter = prior_solutions.iter();
                let transactions_iter = transaction_ids.iter();
                let prior_transactions_iter = prior_transactions.iter();
                let aborted_tx_iter = aborted_transaction_ids.iter();

                // Convert compact certificate to batch certificate.
                let batch_certificate = certificate.into_batch_certificate(
                    ratifications_iter,
                    solutions_iter,
                    prior_solutions_iter,
                    transactions_iter,
                    prior_transactions_iter,
                    aborted_tx_iter,
                )?;
                batch_certificates.insert(batch_certificate);
            }
            batch_subdag.insert(round, batch_certificates);
        }

        // Return the batch certificates.
        Ok(Self::Full { subdag: batch_subdag, election_certificate_ids })
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
            previous_certificate_ids.insert(certificate.id());
            subdag.entry(starting_round).or_default().insert(certificate);
        }

        // Process the middle round.
        let mut previous_certificate_ids_2 = IndexSet::new();
        for _ in 0..QUORUM_THRESHOLD {
            let certificate =
                narwhal_batch_certificate::test_helpers::sample_batch_certificate_for_round_with_previous_certificate_ids(starting_round + 1, previous_certificate_ids.clone(), rng);
            previous_certificate_ids_2.insert(certificate.id());
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

        // Initialize the election certificate IDs.
        let mut election_certificate_ids = IndexSet::new();
        for _ in 0..AVAILABILITY_THRESHOLD {
            election_certificate_ids.insert(rng.gen());
        }

        // Return the subdag.
        Subdag::from_full(subdag, election_certificate_ids).unwrap()
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
