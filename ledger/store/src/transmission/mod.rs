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

use crate::{
    atomic_batch_scope,
    cow_to_cloned,
    helpers::{NestedMap, NestedMapRead},
};
use console::network::prelude::*;
use ledger_narwhal_transmission::Transmission;
use ledger_narwhal_transmission_id::TransmissionID;

use anyhow::Result;
use std::marker::PhantomData;

/// A trait for transmission storage.
pub trait TransmissionStorage<N: Network>: 'static + Clone + Send + Sync {
    /// The mapping of `round number` to `[(transmission ID, transmission)]`.
    type TransmissionMap: for<'a> NestedMap<'a, u64, TransmissionID<N>, Transmission<N>>;

    /// Initializes the transmission storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Initializes the test-variant of the storage.
    #[cfg(any(test, feature = "test"))]
    fn open_testing(temp_dir: std::path::PathBuf, dev: Option<u16>) -> Result<Self>;

    /// Returns the transmission map.
    fn transmission_map(&self) -> &Self::TransmissionMap;

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16>;

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.transmission_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.transmission_map().is_atomic_in_progress()
    }

    /// Checkpoints the atomic batch.
    fn atomic_checkpoint(&self) {
        self.transmission_map().atomic_checkpoint();
    }

    /// Clears the latest atomic batch checkpoint.
    fn clear_latest_checkpoint(&self) {
        self.transmission_map().clear_latest_checkpoint();
    }

    /// Rewinds the atomic batch to the previous checkpoint.
    fn atomic_rewind(&self) {
        self.transmission_map().atomic_rewind();
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.transmission_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.transmission_map().finish_atomic()
    }

    /// Stores the given `(transmission ID, transmission)` pair into storage.
    /// If the `transmission ID` already exists, the method returns an error.
    fn insert_transmission(
        &self,
        round: u64,
        transmission_id: TransmissionID<N>,
        transmission: Transmission<N>,
    ) -> Result<()> {
        atomic_batch_scope!(self, {
            // Insert the transmission for the round.
            self.transmission_map().insert(round, transmission_id, transmission)?;

            Ok(())
        })
    }

    /// Removes the transmission for the given `round` and `transmission ID` from storage.
    fn remove_transmission(&self, round: u64, transmission_id: TransmissionID<N>) -> Result<()> {
        atomic_batch_scope!(self, {
            // Insert the transmission for the round.
            self.transmission_map().remove_key(&round, &transmission_id)?;

            Ok(())
        })
    }

    /// Stores the given `(transmission ID, transmission)` pairs into storage.
    fn insert_transmissions(&self, round: u64, transmissions: Vec<(TransmissionID<N>, Transmission<N>)>) -> Result<()> {
        atomic_batch_scope!(self, {
            for (transmission_id, transmission) in transmissions.into_iter() {
                // Insert the transmission for the round.
                self.transmission_map().insert(round, transmission_id, transmission)?
            }

            Ok(())
        })
    }

    /// Removes the transmissions for the given `round` from storage.
    fn remove_transmissions(&self, round: u64) -> Result<()> {
        atomic_batch_scope!(self, {
            // Remove the round transmissions.
            self.transmission_map().remove_map(&round)?;

            Ok(())
        })
    }

    /// Returns `true` if the given `round` and `transmission ID` exist.
    fn contains_transmission_confirmed(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.transmission_map().contains_key_confirmed(&round, transmission_id)
    }

    /// Returns `true` if the given `round` and `transmission ID` exist.
    fn contains_transmission_speculative(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.transmission_map().contains_key_speculative(&round, transmission_id)
    }

    /// Returns the confirmed transmission entries for the given `round`.
    fn get_transmissions_confirmed(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        // Retrieve the transmissions for the mapping.
        self.transmission_map().get_map_confirmed(&round)
    }

    /// Returns the speculative transmission entries for the given `round`.
    fn get_transmissions_speculative(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        // Retrieve the transmissions for the mapping.
        self.transmission_map().get_map_speculative(&round)
    }

    /// Returns the confirmed transmission for the given `round` and `transmission ID`.
    fn get_transmission_confirmed(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        match self.transmission_map().get_value_confirmed(&round, transmission_id)? {
            Some(transmission) => Ok(Some(cow_to_cloned!(transmission))),
            None => Ok(None),
        }
    }

    /// Returns the speculative transmission for the given `round` and `transmission ID`.
    fn get_transmission_speculative(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        match self.transmission_map().get_value_speculative(&round, transmission_id)? {
            Some(transmission) => Ok(Some(cow_to_cloned!(transmission))),
            None => Ok(None),
        }
    }
}

/// The transmission store.
#[derive(Clone)]
pub struct TransmissionStore<N: Network, T: TransmissionStorage<N>> {
    /// The transmission storage.
    storage: T,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, T: TransmissionStorage<N>> TransmissionStore<N, T> {
    /// Initializes the transmission store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the transmission storage.
        let storage = T::open(dev)?;

        // Return the transmission store.
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Initializes the test-variant of the storage.
    #[cfg(any(test, feature = "test"))]
    pub fn open_testing(temp_dir: std::path::PathBuf, dev: Option<u16>) -> Result<Self> {
        Self::from(T::open_testing(temp_dir, dev)?)
    }

    /// Initializes a transmission store from storage.
    pub fn from(storage: T) -> Result<Self> {
        // Return the transmission store.
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

impl<N: Network, T: TransmissionStorage<N>> TransmissionStore<N, T> {
    /// Stores the given `(round, transmission)` pair into storage.
    /// If the `transmission ID` already exists, the method returns an error.
    fn insert_transmission(
        &self,
        round: u64,
        transmission_id: TransmissionID<N>,
        transmission: Transmission<N>,
    ) -> Result<()> {
        self.storage.insert_transmission(round, transmission_id, transmission)
    }

    /// Removes the transmission for the given `round` and `transmission ID` from storage.
    fn remove_transmission(&self, round: u64, transmission_id: TransmissionID<N>) -> Result<()> {
        self.storage.remove_transmission(round, transmission_id)
    }

    /// Stores the given `(round, transmissions)` pair into storage.
    fn insert_transmissions(&self, round: u64, transmissions: Vec<(TransmissionID<N>, Transmission<N>)>) -> Result<()> {
        self.storage.insert_transmissions(round, transmissions)
    }

    /// Removes the transmissions for the given `round` from storage.
    fn remove_transmissions(&self, round: u64) -> Result<()> {
        self.storage.remove_transmissions(round)
    }
}

impl<N: Network, T: TransmissionStorage<N>> TransmissionStore<N, T> {
    /// Returns `true` if the given `round` and `transmission ID` exist.
    fn contains_transmission_confirmed(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.storage.contains_transmission_confirmed(round, transmission_id)
    }

    /// Returns `true` if the given `round` and `transmission ID` exist.
    fn contains_transmission_speculative(&self, round: u64, transmission_id: &TransmissionID<N>) -> Result<bool> {
        self.storage.contains_transmission_speculative(round, transmission_id)
    }
}

impl<N: Network, T: TransmissionStorage<N>> TransmissionStore<N, T> {
    /// Returns the confirmed transmission entries for the given `round`.
    fn get_transmissions_confirmed(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        self.storage.get_transmissions_confirmed(round)
    }

    /// Returns the speculative transmission entries for the given `round`.
    fn get_transmissions_speculative(&self, round: u64) -> Result<Vec<(TransmissionID<N>, Transmission<N>)>> {
        self.storage.get_transmissions_speculative(round)
    }

    /// Returns the confirmed transmission for the given `round` and `transmission ID`.
    fn get_transmission_confirmed(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        self.storage.get_transmission_confirmed(round, transmission_id)
    }

    /// Returns the speculative transmission for the given `round` and `transmission ID`.
    fn get_transmission_speculative(
        &self,
        round: u64,
        transmission_id: &TransmissionID<N>,
    ) -> Result<Option<Transmission<N>>> {
        self.storage.get_transmission_speculative(round, transmission_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::helpers::memory::TransmissionMemory;
    use console::network::Testnet3;
    use ledger_narwhal_transmission::test_helpers::sample_transmissions;
    use ledger_narwhal_transmission_id::test_helpers::sample_transmission_ids;

    use std::collections::HashMap;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_insert_get_remove_transmission() {
        let rng = &mut TestRng::default();

        // Sample a round number, transmissions and transmission ids.
        let round: u64 = rng.gen();
        let transmissions = sample_transmissions(rng);
        let transmission_ids = sample_transmission_ids(rng);

        // Initialize a new transmission store.
        let transmission_store = TransmissionStore::<CurrentNetwork, TransmissionMemory<_>>::open(None).unwrap();

        for (transmission_id, transmission) in transmission_ids.iter().zip_eq(transmissions) {
            // Insert the transmission.
            transmission_store.insert_transmission(round, *transmission_id, transmission.clone()).unwrap();

            // Find the transmission.
            let candidate = transmission_store.get_transmission_confirmed(round, transmission_id).unwrap();
            assert_eq!(Some(transmission), candidate);

            // Remove the transmission.
            transmission_store.remove_transmission(round, *transmission_id).unwrap();

            // Ensure the transmission ID is not found.
            let candidate = transmission_store.get_transmission_confirmed(round, transmission_id).unwrap();
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

        let transmissions = transmission_ids.into_iter().zip_eq(transmissions).collect::<Vec<(_, _)>>();

        // Initialize a new transmission store.
        let transmission_store = TransmissionStore::<CurrentNetwork, TransmissionMemory<_>>::open(None).unwrap();

        // Find the transmissions.
        let candidate = transmission_store.get_transmissions_confirmed(round).unwrap();
        assert!(candidate.is_empty());

        // Insert the transmissions.
        transmission_store.insert_transmissions(round, transmissions.clone()).unwrap();

        // Find the transmissions.
        let candidate = transmission_store.get_transmissions_confirmed(round).unwrap();
        assert_eq!(
            transmissions.iter().cloned().collect::<HashMap<_, _>>(),
            candidate.iter().cloned().collect::<HashMap<_, _>>()
        );

        // Remove the transmissions
        transmission_store.remove_transmissions(round).unwrap();

        // Ensure the transmissions are not found.
        let candidate = transmission_store.get_transmissions_confirmed(round).unwrap();
        assert!(candidate.is_empty());
    }
}
