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
    block::FinalizeOperation,
    cow_to_cloned,
    cow_to_copied,
    stack::FinalizeStoreTrait,
    store::helpers::{Map, MapRead},
};
use console::{
    network::prelude::*,
    program::{Identifier, Plaintext, ProgramID, Value},
    types::Field,
};

use anyhow::Result;
use core::marker::PhantomData;
use indexmap::{IndexMap, IndexSet};

/// A trait for program state storage. Note: For the program logic, see `DeploymentStorage`.
///
/// We define the `mapping ID := Hash( program ID || mapping name )`,
/// and the `key ID := Hash ( mapping ID || Hash(key) )`,
/// and the `value ID := Hash ( key ID || Hash(value) )`.
///
/// `FinalizeStorage` emulates the following data structure:
/// ```text
/// // (program_id => (mapping_name => (key => value)))
/// BTreeMap<ProgramID<N>, BTreeMap<Identifier<N>, BTreeMap<Key, Value>>>
/// ```
pub trait FinalizeStorage<N: Network>: 'static + Clone + Send + Sync {
    /// The mapping of `program ID` to `[mapping name]`.
    type ProgramIDMap: for<'a> Map<'a, ProgramID<N>, IndexSet<Identifier<N>>>;
    /// The mapping of `(program ID, mapping name)` to `mapping ID`.
    type MappingIDMap: for<'a> Map<'a, (ProgramID<N>, Identifier<N>), Field<N>>;
    /// The mapping of `mapping ID` to `[(key ID, value ID)]`.
    type KeyValueIDMap: for<'a> Map<'a, Field<N>, IndexMap<Field<N>, Field<N>>>;
    /// The mapping of `key ID` to `key`.
    type KeyMap: for<'a> Map<'a, Field<N>, Plaintext<N>>;
    /// The mapping of `key ID` to `value`.
    type ValueMap: for<'a> Map<'a, Field<N>, Value<N>>;

    /// Initializes the program state storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Returns the program ID map.
    fn program_id_map(&self) -> &Self::ProgramIDMap;
    /// Returns the mapping ID map.
    fn mapping_id_map(&self) -> &Self::MappingIDMap;
    /// Returns the key-value ID map.
    fn key_value_id_map(&self) -> &Self::KeyValueIDMap;
    /// Returns the key map.
    fn key_map(&self) -> &Self::KeyMap;
    /// Returns the value map.
    fn value_map(&self) -> &Self::ValueMap;

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16>;

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.program_id_map().start_atomic();
        self.mapping_id_map().start_atomic();
        self.key_value_id_map().start_atomic();
        self.key_map().start_atomic();
        self.value_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.program_id_map().is_atomic_in_progress()
            || self.mapping_id_map().is_atomic_in_progress()
            || self.key_value_id_map().is_atomic_in_progress()
            || self.key_map().is_atomic_in_progress()
            || self.value_map().is_atomic_in_progress()
    }

    /// Checkpoints the atomic batch.
    fn atomic_checkpoint(&self) {
        self.program_id_map().atomic_checkpoint();
        self.mapping_id_map().atomic_checkpoint();
        self.key_value_id_map().atomic_checkpoint();
        self.key_map().atomic_checkpoint();
        self.value_map().atomic_checkpoint();
    }

    /// Clears the latest atomic batch checkpoint.
    fn clear_latest_checkpoint(&self) {
        self.program_id_map().clear_latest_checkpoint();
        self.mapping_id_map().clear_latest_checkpoint();
        self.key_value_id_map().clear_latest_checkpoint();
        self.key_map().clear_latest_checkpoint();
        self.value_map().clear_latest_checkpoint();
    }

    /// Rewinds the atomic batch to the previous checkpoint.
    fn atomic_rewind(&self) {
        self.program_id_map().atomic_rewind();
        self.mapping_id_map().atomic_rewind();
        self.key_value_id_map().atomic_rewind();
        self.key_map().atomic_rewind();
        self.value_map().atomic_rewind();
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.program_id_map().abort_atomic();
        self.mapping_id_map().abort_atomic();
        self.key_value_id_map().abort_atomic();
        self.key_map().abort_atomic();
        self.value_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.program_id_map().finish_atomic()?;
        self.mapping_id_map().finish_atomic()?;
        self.key_value_id_map().finish_atomic()?;
        self.key_map().finish_atomic()?;
        self.value_map().finish_atomic()
    }

    /// Initializes the given `program ID` and `mapping name` in storage.
    /// If the `mapping name` is already initialized, an error is returned.
    fn initialize_mapping(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
    ) -> Result<FinalizeOperation<N>> {
        // Ensure the mapping name does not already exist.
        if self.mapping_id_map().contains_key_speculative(&(*program_id, *mapping_name))? {
            bail!("Illegal operation: mapping '{mapping_name}' already exists in storage - cannot initialize again.")
        }

        // Compute the mapping ID.
        let mapping_id = N::hash_bhp1024(&(program_id, mapping_name).to_bits_le())?;
        // Ensure the mapping ID does not already exist.
        if self.key_value_id_map().contains_key_speculative(&mapping_id)? {
            bail!("Illegal operation: mapping ID '{mapping_id}' already exists in storage - cannot initialize again.")
        }

        // Retrieve the mapping names for the program ID.
        let mut mapping_names = match self.program_id_map().get_speculative(program_id)? {
            // If the program ID already exists, retrieve the mapping names.
            Some(mapping_names) => cow_to_cloned!(mapping_names),
            // If the program ID does not exist, initialize the mapping names.
            None => IndexSet::new(),
        };

        // Ensure the mapping name does not already exist.
        if mapping_names.contains(mapping_name) {
            bail!("Illegal operation: mapping name '{mapping_name}' already exists in storage - cannot re-initialize.")
        }

        // Insert the new mapping name.
        mapping_names.insert(*mapping_name);

        atomic_batch_scope!(self, {
            // Update the program ID map with the new mapping name.
            self.program_id_map().insert(*program_id, mapping_names)?;
            // Initialize the mapping ID map.
            self.mapping_id_map().insert((*program_id, *mapping_name), mapping_id)?;
            // Initialize the key-value ID map.
            self.key_value_id_map().insert(mapping_id, IndexMap::new())?;

            Ok(())
        })?;

        // Return the finalize operation.
        Ok(FinalizeOperation::InitializeMapping(mapping_id))
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `mapping name` is not initialized, an error is returned.
    /// If the `key` already exists, the method returns an error.
    fn insert_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<FinalizeOperation<N>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => bail!("Illegal operation: mapping '{mapping_name}' is not initialized - cannot insert key-value."),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Compute the value ID.
        let value_id = N::hash_bhp1024(&(key_id, N::hash_bhp1024(&value.to_bits_le())?).to_bits_le())?;

        // Ensure the key ID does not already exist.
        if self.key_map().contains_key_speculative(&key_id)? {
            bail!("Illegal operation: key ID '{key_id}' already exists in storage - cannot insert again.")
        }
        // Retrieve the key-value IDs for the mapping ID.
        let mut key_value_ids = match self.key_value_id_map().get_speculative(&mapping_id)? {
            Some(key_value_ids) => cow_to_cloned!(key_value_ids),
            None => bail!("Illegal operation: mapping ID '{mapping_id}' is not initialized - cannot insert key-value."),
        };
        // Ensure the key ID does not already exist.
        if key_value_ids.contains_key(&key_id) {
            bail!("Illegal operation: key ID '{key_id}' already exists in storage - cannot insert key-value.");
        }
        // Insert the new key-value ID.
        key_value_ids.insert(key_id, value_id);

        atomic_batch_scope!(self, {
            // Update the key-value ID map with the new key-value ID.
            self.key_value_id_map().insert(mapping_id, key_value_ids)?;
            // Insert the key.
            self.key_map().insert(key_id, key)?;
            // Insert the value.
            self.value_map().insert(key_id, value)?;

            Ok(())
        })?;

        // Return the finalize operation.
        Ok(FinalizeOperation::InsertKeyValue(mapping_id, key_id, value_id))
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `mapping name` is not initialized, an error is returned.
    /// If the `key` does not exist, the `(key, value)` pair is initialized.
    /// If the `key` already exists, the `value` is overwritten.
    fn update_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<FinalizeOperation<N>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => bail!("Illegal operation: mapping '{mapping_name}' is not initialized - cannot update key-value."),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Compute the value ID.
        let value_id = N::hash_bhp1024(&(key_id, N::hash_bhp1024(&value.to_bits_le())?).to_bits_le())?;

        // Retrieve the key-value IDs for the mapping ID.
        let mut key_value_ids = match self.key_value_id_map().get_speculative(&mapping_id)? {
            Some(key_value_ids) => cow_to_cloned!(key_value_ids),
            None => {
                bail!("Illegal operation: mapping ID '{mapping_id}' is not initialized - cannot update key-value.")
            }
        };
        // If the key ID does not exist, insert it in the key-value ID map.
        if !self.key_map().contains_key_speculative(&key_id)? {
            // Ensure the key ID does not already exist.
            // If this fails, then there is inconsistent state, and likely data corruption.
            if key_value_ids.contains_key(&key_id) {
                bail!("Illegal operation: key ID '{key_id}' already exists in storage - cannot update key-value.");
            }
        }
        // Insert the new key-value ID.
        key_value_ids.insert(key_id, value_id);

        // Retrieve the index of the key ID in the key-value ID map.
        let index = match key_value_ids.get_index_of(&key_id) {
            Some(index) => u64::try_from(index)?,
            None => bail!("Illegal operation: key ID '{key_id}' does not exist in storage - cannot finalize."),
        };

        atomic_batch_scope!(self, {
            // Update the key-value ID map with the new key-value ID.
            self.key_value_id_map().insert(mapping_id, key_value_ids)?;
            // Insert the key.
            self.key_map().insert(key_id, key)?;
            // Insert the value.
            self.value_map().insert(key_id, value)?;

            Ok(())
        })?;

        // Return the finalize operation.
        Ok(FinalizeOperation::UpdateKeyValue(mapping_id, index, key_id, value_id))
    }

    /// Removes the key-value pair for the given `program ID`, `mapping name`, and `key` from storage.
    fn remove_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<FinalizeOperation<N>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => bail!("Illegal operation: mapping '{mapping_name}' is not initialized - cannot remove key-value."),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Retrieve the key-value IDs for the mapping ID.
        let mut key_value_ids = match self.key_value_id_map().get_speculative(&mapping_id)? {
            Some(key_value_ids) => cow_to_cloned!(key_value_ids),
            None => bail!("Illegal operation: mapping ID '{mapping_id}' is not initialized - cannot remove key-value."),
        };
        // Ensure the key ID exists.
        if !key_value_ids.contains_key(&key_id) {
            bail!("Illegal operation: key ID '{key_id}' does not exist in storage - cannot remove key-value.");
        }

        // Retrieve the index of the key ID in the key-value ID map.
        let index = match key_value_ids.get_index_of(&key_id) {
            Some(index) => u64::try_from(index)?,
            None => bail!("Illegal operation: key ID '{key_id}' does not exist in storage - cannot finalize."),
        };

        // Remove the key ID.
        key_value_ids.remove(&key_id);

        atomic_batch_scope!(self, {
            // Update the key-value ID map with the new key ID.
            self.key_value_id_map().insert(mapping_id, key_value_ids)?;
            // Remove the key.
            self.key_map().remove(&key_id)?;
            // Remove the value.
            self.value_map().remove(&key_id)?;

            Ok(())
        })?;

        // Return the finalize operation.
        Ok(FinalizeOperation::RemoveKeyValue(mapping_id, index))
    }

    /// Removes the mapping for the given `program ID` and `mapping name` from storage,
    /// along with all associated key-value pairs in storage.
    fn remove_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<FinalizeOperation<N>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => bail!("Illegal operation: mapping '{mapping_name}' is not initialized - cannot remove mapping."),
        };
        // Retrieve the key-value IDs for the mapping ID.
        let key_value_ids = match self.key_value_id_map().get_speculative(&mapping_id)? {
            Some(key_value_ids) => key_value_ids,
            None => bail!("Illegal operation: mapping ID '{mapping_id}' is not initialized - cannot remove mapping."),
        };

        // Retrieve the mapping names.
        let mut mapping_names = match self.program_id_map().get_speculative(program_id)? {
            Some(mapping_names) => cow_to_cloned!(mapping_names),
            None => bail!("Illegal operation: program ID '{program_id}' is not initialized - cannot remove mapping."),
        };
        // Ensure the mapping name exists.
        if !mapping_names.contains(mapping_name) {
            bail!("Illegal operation: mapping '{mapping_name}' does not exist in storage - cannot remove mapping.");
        }
        // Remove the mapping name.
        mapping_names.remove(mapping_name);

        atomic_batch_scope!(self, {
            // Update the mapping names.
            self.program_id_map().insert(*program_id, mapping_names)?;
            // Remove the mapping ID.
            self.mapping_id_map().remove(&(*program_id, *mapping_name))?;
            // Remove the key IDs.
            self.key_value_id_map().remove(&mapping_id)?;
            // Remove the keys.
            for key_id in key_value_ids.keys() {
                self.key_map().remove(key_id)?;
                self.value_map().remove(key_id)?;
            }

            Ok(())
        })?;

        // Return the finalize operation.
        Ok(FinalizeOperation::RemoveMapping(mapping_id))
    }

    /// Removes the program for the given `program ID` from storage,
    /// along with all associated mappings and key-value pairs in storage.
    fn remove_program(&self, program_id: &ProgramID<N>) -> Result<()> {
        // Retrieve the mapping names.
        let mapping_names = match self.program_id_map().get_speculative(program_id)? {
            Some(mapping_names) => mapping_names,
            None => bail!("Illegal operation: program ID '{program_id}' is not initialized - cannot remove mapping."),
        };

        atomic_batch_scope!(self, {
            // Update the mapping names.
            self.program_id_map().remove(program_id)?;

            // Remove each mapping.
            for mapping_name in mapping_names.iter() {
                // Retrieve the mapping ID.
                let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
                    Some(mapping_id) => mapping_id,
                    None => {
                        bail!("Illegal operation: mapping '{mapping_name}' is not initialized - cannot remove mapping.")
                    }
                };
                // Retrieve the key-value IDs for the mapping ID.
                let key_value_ids = match self.key_value_id_map().get_speculative(&mapping_id)? {
                    Some(key_value_ids) => key_value_ids,
                    None => {
                        bail!(
                            "Illegal operation: mapping ID '{mapping_id}' is not initialized - cannot remove mapping."
                        )
                    }
                };

                // Remove the mapping ID.
                self.mapping_id_map().remove(&(*program_id, *mapping_name))?;
                // Remove the key IDs.
                self.key_value_id_map().remove(&mapping_id)?;
                // Remove the keys.
                for key_id in key_value_ids.keys() {
                    self.key_map().remove(key_id)?;
                    self.value_map().remove(key_id)?;
                }
            }

            Ok(())
        })
    }

    /// Returns `true` if the given `program ID` exist.
    fn contains_program_confirmed(&self, program_id: &ProgramID<N>) -> Result<bool> {
        self.program_id_map().contains_key_confirmed(program_id)
    }

    /// Returns `true` if the given `program ID` and `mapping name` exist.
    fn contains_mapping_confirmed(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<bool> {
        self.mapping_id_map().contains_key_confirmed(&(*program_id, *mapping_name))
    }

    /// Returns `true` if the given `program ID`, `mapping name`, and `key` exist.
    fn contains_key_confirmed(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<bool> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => return Ok(false),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Return whether the key ID exists.
        self.key_map().contains_key_confirmed(&key_id)
    }

    /// Returns `true` if the given `program ID`, `mapping name`, and `key` exist.
    fn contains_key_speculative(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<bool> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => return Ok(false),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Return whether the key ID exists.
        self.key_map().contains_key_speculative(&key_id)
    }

    /// Returns the confirmed mapping names for the given `program ID`.
    fn get_mapping_names_confirmed(&self, program_id: &ProgramID<N>) -> Result<Option<IndexSet<Identifier<N>>>> {
        // Retrieve the mapping names.
        match self.program_id_map().get_confirmed(program_id)? {
            Some(names) => Ok(Some(cow_to_cloned!(names))),
            None => Ok(None),
        }
    }

    /// Returns the speculative mapping names for the given `program ID`.
    fn get_mapping_names_speculative(&self, program_id: &ProgramID<N>) -> Result<Option<IndexSet<Identifier<N>>>> {
        // Retrieve the mapping names.
        match self.program_id_map().get_speculative(program_id)? {
            Some(names) => Ok(Some(cow_to_cloned!(names))),
            None => Ok(None),
        }
    }

    /// Returns the confirmed mapping ID for the given `program ID` and `mapping name`.
    fn get_mapping_id_confirmed(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
    ) -> Result<Option<Field<N>>> {
        match self.mapping_id_map().get_confirmed(&(*program_id, *mapping_name))? {
            Some(mapping_id) => Ok(Some(cow_to_copied!(mapping_id))),
            None => Ok(None),
        }
    }

    /// Returns the speculative mapping ID for the given `program ID` and `mapping name`.
    fn get_mapping_id_speculative(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
    ) -> Result<Option<Field<N>>> {
        match self.mapping_id_map().get_speculative(&(*program_id, *mapping_name))? {
            Some(mapping_id) => Ok(Some(cow_to_copied!(mapping_id))),
            None => Ok(None),
        }
    }

    /// Returns the confirmed key ID for the given `program ID`, `mapping name`, and `key`.
    fn get_key_id_confirmed(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Field<N>>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_confirmed(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => return Ok(None),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Ensure the key ID exists.
        match self.key_map().contains_key_confirmed(&key_id)? {
            true => Ok(Some(key_id)),
            false => Ok(None),
        }
    }

    /// Returns the speculative key ID for the given `program ID`, `mapping name`, and `key`.
    fn get_key_id_speculative(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Field<N>>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id_speculative(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => return Ok(None),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Ensure the key ID exists.
        match self.key_map().contains_key_speculative(&key_id)? {
            true => Ok(Some(key_id)),
            false => Ok(None),
        }
    }

    /// Returns the speculative key for the given `key ID`.
    fn get_key_speculative(&self, key_id: &Field<N>) -> Result<Option<Plaintext<N>>> {
        match self.key_map().get_speculative(key_id)? {
            Some(key) => Ok(Some(cow_to_cloned!(key))),
            None => Ok(None),
        }
    }

    /// Returns the confirmed value for the given `program ID`, `mapping name`, and `key`.
    fn get_value_confirmed(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        // Retrieve the key ID.
        match self.get_key_id_confirmed(program_id, mapping_name, key)? {
            // Retrieve the value.
            Some(key_id) => self.get_value_from_key_id_confirmed(&key_id),
            None => Ok(None),
        }
    }

    /// Returns the speculative value for the given `program ID`, `mapping name`, and `key`.
    fn get_value_speculative(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        // Retrieve the key ID.
        match self.get_key_id_speculative(program_id, mapping_name, key)? {
            // Retrieve the value.
            Some(key_id) => self.get_value_from_key_id_speculative(&key_id),
            None => Ok(None),
        }
    }

    /// Returns the confirmed value for the given `key ID`.
    fn get_value_from_key_id_confirmed(&self, key_id: &Field<N>) -> Result<Option<Value<N>>> {
        match self.value_map().get_confirmed(key_id)? {
            Some(value) => Ok(Some(cow_to_cloned!(value))),
            None => Ok(None),
        }
    }

    /// Returns the speculative value for the given `key ID`.
    fn get_value_from_key_id_speculative(&self, key_id: &Field<N>) -> Result<Option<Value<N>>> {
        match self.value_map().get_speculative(key_id)? {
            Some(value) => Ok(Some(cow_to_cloned!(value))),
            None => Ok(None),
        }
    }
}

/// The finalize store.
#[derive(Clone)]
pub struct FinalizeStore<N: Network, P: FinalizeStorage<N>> {
    /// The finalize storage.
    storage: P,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, P: FinalizeStorage<N>> FinalizeStore<N, P> {
    /// Initializes the finalize store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        Self::from(P::open(dev)?)
    }

    /// Initializes a finalize store from storage.
    pub fn from(storage: P) -> Result<Self> {
        // Return the finalize store.
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

impl<N: Network, P: FinalizeStorage<N>> FinalizeStoreTrait<N> for FinalizeStore<N, P> {
    /// Returns `true` if the given `program ID` and `mapping name` exist.
    fn contains_mapping_confirmed(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<bool> {
        self.storage.contains_mapping_confirmed(program_id, mapping_name)
    }

    /// Returns `true` if the given `program ID`, `mapping name`, and `key` exist.
    fn contains_key_speculative(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<bool> {
        self.storage.contains_key_speculative(program_id, mapping_name, key)
    }

    /// Returns the speculative value for the given `program ID`, `mapping name`, and `key`.
    fn get_value_speculative(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        self.storage.get_value_speculative(program_id, mapping_name, key)
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `mapping name` is not initialized, an error is returned.
    /// If the `key` already exists, the method returns an error.
    fn insert_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<FinalizeOperation<N>> {
        self.storage.insert_key_value(program_id, mapping_name, key, value)
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `mapping name` is not initialized, an error is returned.
    /// If the `key` does not exist, the `(key, value)` pair is initialized.
    /// If the `key` already exists, the `value` is overwritten.
    fn update_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<FinalizeOperation<N>> {
        self.storage.update_key_value(program_id, mapping_name, key, value)
    }

    /// Removes the key-value pair for the given `program ID`, `mapping name`, and `key` from storage.
    fn remove_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<FinalizeOperation<N>> {
        self.storage.remove_key_value(program_id, mapping_name, key)
    }
}

impl<N: Network, P: FinalizeStorage<N>> FinalizeStore<N, P> {
    /// Initializes the given `program ID` and `mapping name` in storage.
    /// If the `mapping name` is already initialized, an error is returned.
    pub fn initialize_mapping(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
    ) -> Result<FinalizeOperation<N>> {
        self.storage.initialize_mapping(program_id, mapping_name)
    }

    /// Removes the mapping for the given `program ID` and `mapping name` from storage,
    /// along with all associated key-value pairs in storage.
    pub fn remove_mapping(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
    ) -> Result<FinalizeOperation<N>> {
        self.storage.remove_mapping(program_id, mapping_name)
    }

    /// Removes the program for the given `program ID` from storage,
    /// along with all associated mappings and key-value pairs in storage.
    pub fn remove_program(&self, program_id: &ProgramID<N>) -> Result<()> {
        self.storage.remove_program(program_id)
    }
}

impl<N: Network, P: FinalizeStorage<N>> FinalizeStore<N, P> {
    /// Returns `true` if the given `program ID` exist.
    pub fn contains_program_confirmed(&self, program_id: &ProgramID<N>) -> Result<bool> {
        self.storage.contains_program_confirmed(program_id)
    }

    /// Returns `true` if the given `program ID`, `mapping name`, and `key` exist.
    pub fn contains_key_confirmed(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<bool> {
        self.storage.contains_key_confirmed(program_id, mapping_name, key)
    }
}

impl<N: Network, P: FinalizeStorage<N>> FinalizeStore<N, P> {
    /// Returns the confirmed mapping names for the given `program ID`.
    pub fn get_mapping_names_confirmed(&self, program_id: &ProgramID<N>) -> Result<Option<IndexSet<Identifier<N>>>> {
        self.storage.get_mapping_names_confirmed(program_id)
    }

    /// Returns the speculative mapping names for the given `program ID`.
    #[deprecated]
    pub fn get_mapping_names_speculative(&self, program_id: &ProgramID<N>) -> Result<Option<IndexSet<Identifier<N>>>> {
        self.storage.get_mapping_names_speculative(program_id)
    }

    /// Returns the confirmed value for the given `program ID`, `mapping name`, and `key`.
    pub fn get_value_confirmed(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        self.storage.get_value_confirmed(program_id, mapping_name, key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::helpers::memory::FinalizeMemory;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Checks `initialize_mapping`, `insert_key_value`, `remove_key_value`, and `remove_mapping`.
    fn check_initialize_insert_remove<N: Network>(
        finalize_store: &FinalizeStore<N, FinalizeMemory<N>>,
        program_id: ProgramID<N>,
        mapping_name: Identifier<N>,
    ) {
        // Prepare a key and value.
        let key = Plaintext::from_str("123456789field").unwrap();
        let value = Value::from_str("987654321u128").unwrap();

        // Ensure the program ID does not exist.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        finalize_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key did not get initialized.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

        // Insert a (key, value) pair.
        finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key got initialized.
        assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns Some(value).
        assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());

        // Ensure removing the key succeeds.
        finalize_store.remove_key_value(&program_id, &mapping_name, &key).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key got removed.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the mapping succeeds.
        finalize_store.remove_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the program succeeds.
        finalize_store.remove_program(&program_id).unwrap();
        // Ensure the program ID is no longer initialized.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is still no longer initialized.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
    }

    /// Checks `initialize_mapping`, `update_key_value`, `remove_key_value`, and `remove_mapping`.
    fn check_initialize_update_remove<N: Network>(
        finalize_store: &FinalizeStore<N, FinalizeMemory<N>>,
        program_id: ProgramID<N>,
        mapping_name: Identifier<N>,
    ) {
        // Prepare a key and value.
        let key = Plaintext::from_str("123456789field").unwrap();
        let value = Value::from_str("987654321u128").unwrap();

        // Ensure the program ID does not exist.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        finalize_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key did not get initialized.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

        // Update a (key, value) pair.
        finalize_store.update_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key got initialized.
        assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns Some(value).
        assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());

        // Ensure calling `insert_key_value` with the same key and value fails.
        assert!(finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).is_err());
        // Ensure the key is still initialized.
        assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns Some(value).
        assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());

        // Ensure calling `update_key_value` with the same key and value succeeds.
        finalize_store.update_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
        // Ensure the key is still initialized.
        assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns Some(value).
        assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());

        {
            // Prepare the same key and different value.
            let new_value = Value::from_str("123456789u128").unwrap();

            // Ensure calling `insert_key_value` with a different key and value fails.
            assert!(
                finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), new_value.clone()).is_err()
            );
            // Ensure the key is still initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value still returns Some(value).
            assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());

            // Ensure calling `update_key_value` with a different key and value succeeds.
            finalize_store.update_key_value(&program_id, &mapping_name, key.clone(), new_value.clone()).unwrap();
            // Ensure the key is still initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(new_value).
            assert_eq!(
                new_value,
                finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap()
            );

            // Ensure calling `update_key_value` with the same key and original value succeeds.
            finalize_store.update_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the key is still initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Ensure removing the key succeeds.
        finalize_store.remove_key_value(&program_id, &mapping_name, &key).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key got removed.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the mapping succeeds.
        finalize_store.remove_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the program succeeds.
        finalize_store.remove_program(&program_id).unwrap();
        // Ensure the program ID is no longer initialized.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is still no longer initialized.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
    }

    #[test]
    fn test_initialize_insert_remove() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new finalize store.
        let program_memory = FinalizeMemory::open(None).unwrap();
        let finalize_store = FinalizeStore::from(program_memory).unwrap();
        // Check the operations.
        check_initialize_insert_remove(&finalize_store, program_id, mapping_name);
    }

    #[test]
    fn test_initialize_update_remove() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new finalize store.
        let program_memory = FinalizeMemory::open(None).unwrap();
        let finalize_store = FinalizeStore::from(program_memory).unwrap();
        // Check the operations.
        check_initialize_update_remove(&finalize_store, program_id, mapping_name);
    }

    #[test]
    fn test_remove_key_value() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new finalize store.
        let program_memory = FinalizeMemory::open(None).unwrap();
        let finalize_store = FinalizeStore::from(program_memory).unwrap();
        // Ensure the program ID does not exist.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        finalize_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());

        // Insert the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key did not get initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

            // Insert the key and value.
            finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the program ID is still initialized.
            assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
            // Ensure the key got initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Remove the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key is still initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());

            // Remove the key-value pair.
            finalize_store.remove_key_value(&program_id, &mapping_name, &key).unwrap();
            // Ensure the program ID is still initialized.
            assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
            // Ensure the key is no longer initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
        }
    }

    #[test]
    fn test_remove_mapping() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new finalize store.
        let program_memory = FinalizeMemory::open(None).unwrap();
        let finalize_store = FinalizeStore::from(program_memory).unwrap();
        // Ensure the program ID does not exist.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        finalize_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());

        // Insert the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key did not get initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

            // Insert the key and value.
            finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the program ID is still initialized.
            assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
            // Ensure the key got initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Remove the mapping.
        finalize_store.remove_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID is still initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());

        // Check the list of keys and values.
        for item in 0..1000 {
            // Prepare the key.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();

            // Ensure the key is no longer initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
        }
    }

    #[test]
    fn test_remove_program() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new finalize store.
        let program_memory = FinalizeMemory::open(None).unwrap();
        let finalize_store = FinalizeStore::from(program_memory).unwrap();
        // Ensure the program ID does not exist.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        finalize_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());

        // Insert the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key did not get initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());

            // Insert the key and value.
            finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the program ID is still initialized.
            assert!(finalize_store.contains_program_confirmed(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
            // Ensure the key got initialized.
            assert!(finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Remove the program.
        finalize_store.remove_program(&program_id).unwrap();
        // Ensure the program ID is no longer initialized.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());

        // Check the list of keys and values.
        for item in 0..1000 {
            // Prepare the key.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();

            // Ensure the key is no longer initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
        }
    }

    #[test]
    fn test_must_initialize_first() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new finalize store.
        let program_memory = FinalizeMemory::open(None).unwrap();
        let finalize_store = FinalizeStore::from(program_memory).unwrap();
        // Ensure the program ID does not exist.
        assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());

        {
            // Ensure inserting a (key, value) before initializing the mapping fails.
            let key = Plaintext::from_str("123456789field").unwrap();
            let value = Value::from_str("987654321u128").unwrap();
            assert!(finalize_store.insert_key_value(&program_id, &mapping_name, key.clone(), value).is_err());

            // Ensure the program ID did not get initialized.
            assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
            // Ensure the mapping name did not get initialized.
            assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
            // Ensure the key did not get initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
            // Ensure removing an un-initialized key fails.
            assert!(finalize_store.remove_key_value(&program_id, &mapping_name, &key).is_err());
            // Ensure removing an un-initialized mapping fails.
            assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());
        }
        {
            // Ensure updating a (key, value) before initializing the mapping fails.
            let key = Plaintext::from_str("987654321field").unwrap();
            let value = Value::from_str("123456789u128").unwrap();
            assert!(finalize_store.update_key_value(&program_id, &mapping_name, key.clone(), value).is_err());

            // Ensure the program ID did not get initialized.
            assert!(!finalize_store.contains_program_confirmed(&program_id).unwrap());
            // Ensure the mapping name did not get initialized.
            assert!(!finalize_store.contains_mapping_confirmed(&program_id, &mapping_name).unwrap());
            // Ensure the key did not get initialized.
            assert!(!finalize_store.contains_key_confirmed(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(finalize_store.get_value_speculative(&program_id, &mapping_name, &key).unwrap().is_none());
            // Ensure removing an un-initialized key fails.
            assert!(finalize_store.remove_key_value(&program_id, &mapping_name, &key).is_err());
            // Ensure removing an un-initialized mapping fails.
            assert!(finalize_store.remove_mapping(&program_id, &mapping_name).is_err());
        }

        // Ensure finalize storage still behaves correctly after the above operations.
        check_initialize_insert_remove(&finalize_store, program_id, mapping_name);
        check_initialize_update_remove(&finalize_store, program_id, mapping_name);
    }
}
