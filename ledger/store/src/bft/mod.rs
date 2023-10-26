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

mod transmission;
pub use transmission::*;

use console::network::prelude::*;
use ledger_narwhal_transmission::Transmission;
use ledger_narwhal_transmission_id::TransmissionID;

use anyhow::Result;
use std::marker::PhantomData;

/// A trait for BFT storage.
pub trait BFTStorage<N: Network>: 'static + Clone + Send + Sync {
    /// The mapping of `round number => transmission ID => transmission`.
    type TransmissionStorage: TransmissionStorage<N>;

    /// Initializes the BFT storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Initializes the test-variant of the storage.
    #[cfg(any(test, feature = "test"))]
    fn open_testing(temp_dir: std::path::PathBuf, dev: Option<u16>) -> Result<Self>;

    /// Returns the transmission store.
    fn transmission_store(&self) -> &TransmissionStore<N, Self::TransmissionStorage>;

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.transmission_store().dev()
    }

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.transmission_store().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.transmission_store().is_atomic_in_progress()
    }

    /// Checkpoints the atomic batch.
    fn atomic_checkpoint(&self) {
        self.transmission_store().atomic_checkpoint();
    }

    /// Clears the latest atomic batch checkpoint.
    fn clear_latest_checkpoint(&self) {
        self.transmission_store().clear_latest_checkpoint();
    }

    /// Rewinds the atomic batch to the previous checkpoint.
    fn atomic_rewind(&self) {
        self.transmission_store().atomic_rewind();
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.transmission_store().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.transmission_store().finish_atomic()
    }

    /// Stores the given `(transmission ID, transmission)` pair into storage.
    /// If the `transmission ID` already exists, the method returns an error.
    fn insert_transmission(
        &self,
        round: u64,
        transmission_id: TransmissionID<N>,
        transmission: Transmission<N>,
    ) -> Result<()> {
        self.transmission_store().insert_transmission(round, transmission_id, transmission)
    }

    /// Stores the given `(transmission ID, transmission)` pairs into storage.
    fn insert_transmissions(&self, round: u64, transmissions: Vec<(TransmissionID<N>, Transmission<N>)>) -> Result<()> {
        self.transmission_store().insert_transmissions(round, transmissions)
    }

    /// Removes the transmission for the given `round` and `transmission ID` from storage.
    fn remove_transmission(&self, round: u64, transmission_id: TransmissionID<N>) -> Result<()> {
        self.transmission_store().remove_transmission(round, transmission_id)
    }

    /// Removes the transmissions for the given `round` from storage.
    fn remove_transmissions(&self, round: u64) -> Result<()> {
        self.transmission_store().remove_transmissions(round)
    }

    /// Returns `true` if the given `round` and `transmission ID` exist.
    fn contains_transmission_confirmed(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.transmission_store().contains_transmission_confirmed(round, transmission_id)
    }

    /// Returns `true` if the given `round` and `transmission ID` exist.
    fn contains_transmission_speculative(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.transmission_store().contains_transmission_speculative(round, transmission_id)
    }

    /// Returns the confirmed transmission for the given `round` and `transmission ID`.
    fn get_transmission_confirmed(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        self.transmission_store().get_transmission_confirmed(round, transmission_id)
    }

    /// Returns the speculative transmission for the given `round` and `transmission ID`.
    fn get_transmission_speculative(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        self.transmission_store().get_transmission_speculative(round, transmission_id)
    }

    /// Returns the confirmed transmission entries for the given `round`.
    fn get_transmissions_confirmed(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        self.transmission_store().get_transmissions_confirmed(round)
    }

    /// Returns the speculative transmission entries for the given `round`.
    fn get_transmissions_speculative(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        self.transmission_store().get_transmissions_speculative(round)
    }
}

/// The BFT store.
#[derive(Clone)]
pub struct BFTStore<N: Network, B: BFTStorage<N>> {
    /// The BFT storage.
    storage: B,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, B: BFTStorage<N>> BFTStore<N, B> {
    /// Initializes the transmission store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the BFT storage.
        let storage = B::open(dev)?;
        // Return the BFT store.
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Initializes the test-variant of the storage.
    #[cfg(any(test, feature = "test"))]
    pub fn open_testing(temp_dir: std::path::PathBuf, dev: Option<u16>) -> Result<Self> {
        Self::from(B::open_testing(temp_dir, dev)?)
    }

    /// Initializes a BFT store from storage.
    pub fn from(storage: B) -> Result<Self> {
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.storage.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.storage.is_atomic_in_progress()
    }

    /// Checkpoints the atomic batch.
    pub fn atomic_checkpoint(&self) {
        self.storage.atomic_checkpoint();
    }

    /// Clears the latest atomic batch checkpoint.
    pub fn clear_latest_checkpoint(&self) {
        self.storage.clear_latest_checkpoint();
    }

    /// Rewinds the atomic batch to the previous checkpoint.
    pub fn atomic_rewind(&self) {
        self.storage.atomic_rewind();
    }

    /// Aborts an atomic batch write operation.
    pub fn abort_atomic(&self) {
        self.storage.abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    pub fn finish_atomic(&self) -> Result<()> {
        self.storage.finish_atomic()
    }

    /// Returns the optional development ID.
    pub fn dev(&self) -> Option<u16> {
        self.storage.dev()
    }
}

impl<N: Network, T: BFTStorage<N>> BFTStore<N, T> {
    /// Stores the given `(round, transmission)` pair into storage.
    /// If the `transmission ID` already exists, the method returns an error.
    pub fn insert_transmission(
        &self,
        round: u64,
        transmission_id: TransmissionID<N>,
        transmission: Transmission<N>,
    ) -> Result<()> {
        self.storage.insert_transmission(round, transmission_id, transmission)
    }

    /// Stores the given `(round, transmissions)` pair into storage.
    pub fn insert_transmissions(
        &self,
        round: u64,
        transmissions: Vec<(TransmissionID<N>, Transmission<N>)>,
    ) -> Result<()> {
        self.storage.insert_transmissions(round, transmissions)
    }

    /// Removes the transmission for the given `round` and `transmission ID` from storage.
    pub fn remove_transmission(&self, round: u64, transmission_id: TransmissionID<N>) -> Result<()> {
        self.storage.remove_transmission(round, transmission_id)
    }

    /// Removes the transmissions for the given `round` from storage.
    pub fn remove_transmissions(&self, round: u64) -> Result<()> {
        self.storage.remove_transmissions(round)
    }
}

impl<N: Network, T: BFTStorage<N>> BFTStore<N, T> {
    /// Returns `true` if the given `round` and `transmission ID` exist.
    pub fn contains_transmission_confirmed(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.storage.contains_transmission_confirmed(round, transmission_id)
    }

    /// Returns `true` if the given `round` and `transmission ID` exist.
    pub fn contains_transmission_speculative(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.storage.contains_transmission_speculative(round, transmission_id)
    }
}

impl<N: Network, T: BFTStorage<N>> BFTStore<N, T> {
    /// Returns the confirmed transmission for the given `round` and `transmission ID`.
    pub fn get_transmission_confirmed(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        self.storage.get_transmission_confirmed(round, transmission_id)
    }

    /// Returns the speculative transmission for the given `round` and `transmission ID`.
    pub fn get_transmission_speculative(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        self.storage.get_transmission_speculative(round, transmission_id)
    }

    /// Returns the confirmed transmission entries for the given `round`.
    pub fn get_transmissions_confirmed(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        self.storage.get_transmissions_confirmed(round)
    }

    /// Returns the speculative transmission entries for the given `round`.
    pub fn get_transmissions_speculative(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        self.storage.get_transmissions_speculative(round)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helpers::memory::BFTMemory;
    use console::network::Testnet3;
    use ledger_narwhal_transmission::test_helpers::sample_transmissions;
    use ledger_narwhal_transmission_id::test_helpers::sample_transmission_ids;

    use std::collections::HashMap;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_insert_get_remove_transmission() {
        let rng = &mut TestRng::default();

        // Sample a round number, transmissions, and transmission ids.
        let round: u64 = rng.gen();
        let transmissions = sample_transmissions(rng);
        let transmission_ids = sample_transmission_ids(rng);
        assert_eq!(transmissions.len(), transmission_ids.len());

        // Initialize a new BFT store.
        let store = BFTStore::<CurrentNetwork, BFTMemory<_>>::open(None).unwrap();

        for (transmission_id, transmission) in transmission_ids.iter().zip_eq(transmissions) {
            // Insert the transmission.
            store.insert_transmission(round, *transmission_id, transmission.clone()).unwrap();

            // Find the transmission.
            let candidate = store.get_transmission_confirmed(round, transmission_id).unwrap();
            assert_eq!(Some(transmission), candidate);

            // Remove the transmission.
            store.remove_transmission(round, *transmission_id).unwrap();

            // Ensure the transmission ID is not found.
            let candidate = store.get_transmission_confirmed(round, transmission_id).unwrap();
            assert_eq!(None, candidate);
        }
    }

    #[test]
    fn test_insert_get_remove_transmissions() {
        let rng = &mut TestRng::default();

        // Sample a round number, transmissions and transmission ids.
        let round: u64 = rng.gen();
        let transmissions = sample_transmissions(rng);
        let transmission_ids = sample_transmission_ids(rng);
        assert_eq!(transmissions.len(), transmission_ids.len());

        let transmissions = transmission_ids.into_iter().zip_eq(transmissions).collect::<Vec<(_, _)>>();

        // Initialize a new BFT store.
        let store = BFTStore::<CurrentNetwork, BFTMemory<_>>::open(None).unwrap();

        // Find the transmissions.
        let candidate = store.get_transmissions_confirmed(round).unwrap();
        assert!(candidate.is_empty());

        // Insert the transmissions.
        store.insert_transmissions(round, transmissions.clone()).unwrap();

        // Find the transmissions.
        let candidate = store.get_transmissions_confirmed(round).unwrap();
        assert_eq!(
            transmissions.iter().cloned().collect::<HashMap<_, _>>(),
            candidate.iter().cloned().collect::<HashMap<_, _>>()
        );

        // Remove the transmissions
        store.remove_transmissions(round).unwrap();

        // Ensure the transmissions are not found.
        let candidate = store.get_transmissions_confirmed(round).unwrap();
        assert!(candidate.is_empty());
    }
}
