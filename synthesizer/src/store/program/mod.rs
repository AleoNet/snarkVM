// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use crate::{
    atomic_write_batch,
    cow_to_cloned,
    cow_to_copied,
    store::helpers::{memory_map::MemoryMap, Map, MapRead},
};
use console::{
    network::prelude::*,
    program::{Identifier, Plaintext, ProgramID, Value},
    types::Field,
};

use anyhow::Result;
use core::marker::PhantomData;
use indexmap::{IndexMap, IndexSet};
use std::collections::BTreeMap;

/// A trait for program state storage. Note: For the program logic, see `DeploymentStorage`.
///
/// We define the `mapping ID := Hash( program ID || mapping name )`,
/// and the `key ID := Hash ( mapping ID || Hash(key) )`,
/// and the `value ID := Hash ( key ID || Hash(value) )`.
///
/// `ProgramStorage` emulates the following data structure:
/// ```text
/// // (program_id => (mapping_name => (key => value)))
/// IndexMap<ProgramID<N>, IndexMap<Identifier<N>, IndexMap<Key, Value>>>
/// ```
pub trait ProgramStorage<N: Network>: 'static + Clone + Send + Sync {
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
    fn initialize_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<()> {
        // Ensure the mapping name does not already exist.
        if self.mapping_id_map().contains_key(&(*program_id, *mapping_name))? {
            bail!("Illegal operation: mapping '{mapping_name}' already exists in storage - cannot initialize again.")
        }

        // Compute the mapping ID.
        let mapping_id = N::hash_bhp1024(&(program_id, mapping_name).to_bits_le())?;
        // Ensure the mapping ID does not already exist.
        if self.key_value_id_map().contains_key(&mapping_id)? {
            bail!("Illegal operation: mapping ID '{mapping_id}' already exists in storage - cannot initialize again.")
        }

        // Retrieve the mapping names for the program ID.
        let mut mapping_names = match self.program_id_map().get_speculative(program_id)? {
            // If the program ID already exists, retrieve the mapping names.
            Some(mapping_names) => cow_to_cloned!(mapping_names),
            // If the program ID does not exist, initialize the mapping names.
            None => IndexSet::new(),
        };
        // Insert the new mapping name.
        mapping_names.insert(*mapping_name);

        atomic_write_batch!(self, {
            // Update the program ID map with the new mapping name.
            self.program_id_map().insert(*program_id, mapping_names)?;
            // Initialize the mapping ID map.
            self.mapping_id_map().insert((*program_id, *mapping_name), mapping_id)?;
            // Initialize the key-value ID map.
            self.key_value_id_map().insert(mapping_id, IndexMap::new())?;

            Ok(())
        });

        Ok(())
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `key` already exists, the method returns an error.
    fn insert_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<()> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => bail!("Illegal operation: mapping '{mapping_name}' is not initialized - cannot insert key-value."),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Compute the value ID.
        let value_id = N::hash_bhp1024(&(key_id, N::hash_bhp1024(&value.to_bits_le())?).to_bits_le())?;

        // Ensure the key ID does not already exist.
        if self.key_map().contains_key(&key_id)? {
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

        atomic_write_batch!(self, {
            // Update the key-value ID map with the new key-value ID.
            self.key_value_id_map().insert(mapping_id, key_value_ids)?;
            // Insert the key.
            self.key_map().insert(key_id, key)?;
            // Insert the value.
            self.value_map().insert(key_id, value)?;

            Ok(())
        });

        Ok(())
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `key` does not exist, the `(key, value)` pair is initialized.
    /// If the `key` already exists, the `value` is overwritten.
    fn update_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<()> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
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
        if !self.key_map().contains_key(&key_id)? {
            // Ensure the key ID does not already exist.
            // If this fails, then there is inconsistent state, and likely data corruption.
            if key_value_ids.contains_key(&key_id) {
                bail!("Illegal operation: key ID '{key_id}' already exists in storage - cannot update key-value.");
            }
        }
        // Insert the new key-value ID.
        key_value_ids.insert(key_id, value_id);

        atomic_write_batch!(self, {
            // Update the key-value ID map with the new key-value ID.
            self.key_value_id_map().insert(mapping_id, key_value_ids)?;
            // Insert the key.
            self.key_map().insert(key_id, key)?;
            // Insert the value.
            self.value_map().insert(key_id, value)?;

            Ok(())
        });

        Ok(())
    }

    /// Removes the key-value pair for the given `program ID`, `mapping name`, and `key` from storage.
    fn remove_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<()> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
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
        // Remove the key ID.
        key_value_ids.remove(&key_id);

        atomic_write_batch!(self, {
            // Update the key-value ID map with the new key ID.
            self.key_value_id_map().insert(mapping_id, key_value_ids)?;
            // Remove the key.
            self.key_map().remove(&key_id)?;
            // Remove the value.
            self.value_map().remove(&key_id)?;

            Ok(())
        });

        Ok(())
    }

    /// Removes the mapping for the given `program ID` and `mapping name` from storage,
    /// along with all associated key-value pairs in storage.
    fn remove_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<()> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
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

        atomic_write_batch!(self, {
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
        });

        Ok(())
    }

    /// Removes the program for the given `program ID` from storage,
    /// along with all associated mappings and key-value pairs in storage.
    fn remove_program(&self, program_id: &ProgramID<N>) -> Result<()> {
        // Retrieve the mapping names.
        let mapping_names = match self.program_id_map().get_speculative(program_id)? {
            Some(mapping_names) => mapping_names,
            None => bail!("Illegal operation: program ID '{program_id}' is not initialized - cannot remove mapping."),
        };

        atomic_write_batch!(self, {
            // Update the mapping names.
            self.program_id_map().remove(program_id)?;

            // Remove each mapping.
            for mapping_name in mapping_names.iter() {
                // Retrieve the mapping ID.
                let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
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
        });

        Ok(())
    }

    /// Returns `true` if the given `program ID` exist.
    fn contains_program(&self, program_id: &ProgramID<N>) -> Result<bool> {
        self.program_id_map().contains_key(program_id)
    }

    /// Returns `true` if the given `program ID` and `mapping name` exist.
    fn contains_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<bool> {
        self.mapping_id_map().contains_key(&(*program_id, *mapping_name))
    }

    /// Returns `true` if the given `program ID`, `mapping name`, and `key` exist.
    fn contains_key(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<bool> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => return Ok(false),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Return whether the key ID exists.
        self.key_map().contains_key(&key_id)
    }

    /// Returns the mapping names for the given `program ID`.
    fn get_mapping_names(&self, program_id: &ProgramID<N>) -> Result<Option<IndexSet<Identifier<N>>>> {
        // Retrieve the mapping names.
        match self.program_id_map().get_speculative(program_id)? {
            Some(names) => Ok(Some(cow_to_cloned!(names))),
            None => Ok(None),
        }
    }

    /// Returns the mapping ID for the given `program ID` and `mapping name`.
    fn get_mapping_id(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<Option<Field<N>>> {
        match self.mapping_id_map().get_speculative(&(*program_id, *mapping_name))? {
            Some(mapping_id) => Ok(Some(cow_to_copied!(mapping_id))),
            None => Ok(None),
        }
    }

    /// Returns the key ID for the given `program ID`, `mapping name`, and `key`.
    fn get_key_id(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Field<N>>> {
        // Retrieve the mapping ID.
        let mapping_id = match self.get_mapping_id(program_id, mapping_name)? {
            Some(mapping_id) => mapping_id,
            None => return Ok(None),
        };
        // Compute the key ID.
        let key_id = N::hash_bhp1024(&(mapping_id, N::hash_bhp1024(&key.to_bits_le())?).to_bits_le())?;
        // Ensure the key ID exists.
        match self.key_map().contains_key(&key_id)? {
            true => Ok(Some(key_id)),
            false => Ok(None),
        }
    }

    /// Returns the key for the given `key ID`.
    fn get_key(&self, key_id: &Field<N>) -> Result<Option<Plaintext<N>>> {
        match self.key_map().get_speculative(key_id)? {
            Some(key) => Ok(Some(cow_to_cloned!(key))),
            None => Ok(None),
        }
    }

    /// Returns the value for the given `program ID`, `mapping name`, and `key`.
    fn get_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        // Retrieve the key ID.
        match self.get_key_id(program_id, mapping_name, key)? {
            // Retrieve the value.
            Some(key_id) => self.get_value_from_key_id(&key_id),
            None => Ok(None),
        }
    }

    /// Returns the value for the given `key ID`.
    fn get_value_from_key_id(&self, key_id: &Field<N>) -> Result<Option<Value<N>>> {
        match self.value_map().get_speculative(key_id)? {
            Some(value) => Ok(Some(cow_to_cloned!(value))),
            None => Ok(None),
        }
    }

    /// Returns the checksum.
    fn get_checksum(&self) -> Result<Field<N>> {
        // Compute all mapping checksums.
        let preimage: BTreeMap<_, _> = self
            .key_value_id_map()
            .iter()
            .map(|(mapping_id, key_value_ids)| {
                // Convert the mapping ID and all value IDs to concatenated bits.
                let preimage = mapping_id
                    .to_bits_le()
                    .into_iter()
                    .chain(key_value_ids.values().flat_map(|value_id| value_id.to_bits_le()));
                // Compute the mapping checksum as `Hash( mapping_id || all value IDs )`.
                let mapping_checksum = N::hash_bhp1024(&preimage.collect::<Vec<_>>())?;
                // Return the mapping ID and mapping checksum.
                Ok::<_, Error>((mapping_id, mapping_checksum.to_bits_le()))
            })
            .try_collect()?;
        // Compute the checksum as `Hash( all mapping checksums )`.
        N::hash_bhp1024(&preimage.into_values().flatten().collect::<Vec<_>>())
    }
}

/// An in-memory program state storage.
#[derive(Clone)]
pub struct ProgramMemory<N: Network> {
    /// The program ID map.
    program_id_map: MemoryMap<ProgramID<N>, IndexSet<Identifier<N>>>,
    /// The mapping ID map.
    mapping_id_map: MemoryMap<(ProgramID<N>, Identifier<N>), Field<N>>,
    /// The key-value ID map.
    key_value_id_map: MemoryMap<Field<N>, IndexMap<Field<N>, Field<N>>>,
    /// The key map.
    key_map: MemoryMap<Field<N>, Plaintext<N>>,
    /// The value map.
    value_map: MemoryMap<Field<N>, Value<N>>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> ProgramStorage<N> for ProgramMemory<N> {
    type ProgramIDMap = MemoryMap<ProgramID<N>, IndexSet<Identifier<N>>>;
    type MappingIDMap = MemoryMap<(ProgramID<N>, Identifier<N>), Field<N>>;
    type KeyValueIDMap = MemoryMap<Field<N>, IndexMap<Field<N>, Field<N>>>;
    type KeyMap = MemoryMap<Field<N>, Plaintext<N>>;
    type ValueMap = MemoryMap<Field<N>, Value<N>>;

    /// Initializes the program state storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            program_id_map: MemoryMap::default(),
            mapping_id_map: MemoryMap::default(),
            key_value_id_map: MemoryMap::default(),
            key_map: MemoryMap::default(),
            value_map: MemoryMap::default(),
            dev,
        })
    }

    /// Returns the program ID map.
    fn program_id_map(&self) -> &Self::ProgramIDMap {
        &self.program_id_map
    }

    /// Returns the mapping ID map.
    fn mapping_id_map(&self) -> &Self::MappingIDMap {
        &self.mapping_id_map
    }

    /// Returns the key-value ID map.
    fn key_value_id_map(&self) -> &Self::KeyValueIDMap {
        &self.key_value_id_map
    }

    /// Returns the key map.
    fn key_map(&self) -> &Self::KeyMap {
        &self.key_map
    }

    /// Returns the value map.
    fn value_map(&self) -> &Self::ValueMap {
        &self.value_map
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}

/// The program store.
#[derive(Clone)]
pub struct ProgramStore<N: Network, P: ProgramStorage<N>> {
    /// The program storage.
    storage: P,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, P: ProgramStorage<N>> ProgramStore<N, P> {
    /// Initializes the program store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self { storage: P::open(dev)?, _phantom: PhantomData })
    }

    /// Initializes a program store from storage.
    pub fn from(storage: P) -> Self {
        Self { storage, _phantom: PhantomData }
    }

    /// Initializes the given `program ID` and `mapping name` in storage.
    pub fn initialize_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<()> {
        self.storage.initialize_mapping(program_id, mapping_name)
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `key` already exists, the method returns an error.
    pub fn insert_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<()> {
        self.storage.insert_key_value(program_id, mapping_name, key, value)
    }

    /// Stores the given `(key, value)` pair at the given `program ID` and `mapping name` in storage.
    /// If the `key` does not exist, the `(key, value)` pair is initialized.
    /// If the `key` already exists, the `value` is overwritten.
    pub fn update_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: Plaintext<N>,
        value: Value<N>,
    ) -> Result<()> {
        self.storage.update_key_value(program_id, mapping_name, key, value)
    }

    /// Removes the key-value pair for the given `program ID`, `mapping name`, and `key` from storage.
    pub fn remove_key_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<()> {
        self.storage.remove_key_value(program_id, mapping_name, key)
    }

    /// Removes the mapping for the given `program ID` and `mapping name` from storage,
    /// along with all associated key-value pairs in storage.
    pub fn remove_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<()> {
        self.storage.remove_mapping(program_id, mapping_name)
    }

    /// Removes the program for the given `program ID` from storage,
    /// along with all associated mappings and key-value pairs in storage.
    pub fn remove_program(&self, program_id: &ProgramID<N>) -> Result<()> {
        self.storage.remove_program(program_id)
    }

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.storage.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.storage.is_atomic_in_progress()
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

impl<N: Network, P: ProgramStorage<N>> ProgramStore<N, P> {
    /// Returns `true` if the given `program ID` exist.
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> Result<bool> {
        self.storage.contains_program(program_id)
    }

    /// Returns `true` if the given `program ID` and `mapping name` exist.
    pub fn contains_mapping(&self, program_id: &ProgramID<N>, mapping_name: &Identifier<N>) -> Result<bool> {
        self.storage.contains_mapping(program_id, mapping_name)
    }

    /// Returns `true` if the given `program ID`, `mapping name`, and `key` exist.
    pub fn contains_key(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<bool> {
        self.storage.contains_key(program_id, mapping_name, key)
    }
}

impl<N: Network, P: ProgramStorage<N>> ProgramStore<N, P> {
    /// Returns the mapping names for the given `program ID`.
    pub fn get_mapping_names(&self, program_id: &ProgramID<N>) -> Result<Option<IndexSet<Identifier<N>>>> {
        self.storage.get_mapping_names(program_id)
    }

    /// Returns the value for the given `program ID`, `mapping name`, and `key`.
    pub fn get_value(
        &self,
        program_id: &ProgramID<N>,
        mapping_name: &Identifier<N>,
        key: &Plaintext<N>,
    ) -> Result<Option<Value<N>>> {
        self.storage.get_value(program_id, mapping_name, key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Checks `initialize_mapping`, `insert_key_value`, `remove_key_value`, and `remove_mapping`.
    fn check_initialize_insert_remove<N: Network>(
        program_store: &ProgramMemory<N>,
        program_id: ProgramID<N>,
        mapping_name: Identifier<N>,
    ) {
        // Prepare a key and value.
        let key = Plaintext::from_str("123456789field").unwrap();
        let value = Value::from_str("987654321u128").unwrap();

        // Ensure the program ID does not exist.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        program_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key did not get initialized.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

        // Insert a (key, value) pair.
        program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key got initialized.
        assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns Some(value).
        assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

        // Ensure removing the key succeeds.
        program_store.remove_key_value(&program_id, &mapping_name, &key).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key got removed.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the mapping succeeds.
        program_store.remove_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the program succeeds.
        program_store.remove_program(&program_id).unwrap();
        // Ensure the program ID is no longer initialized.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is still no longer initialized.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
    }

    /// Checks `initialize_mapping`, `update_key_value`, `remove_key_value`, and `remove_mapping`.
    fn check_initialize_update_remove<N: Network>(
        program_store: &ProgramMemory<N>,
        program_id: ProgramID<N>,
        mapping_name: Identifier<N>,
    ) {
        // Prepare a key and value.
        let key = Plaintext::from_str("123456789field").unwrap();
        let value = Value::from_str("987654321u128").unwrap();

        // Ensure the program ID does not exist.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        program_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key did not get initialized.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

        // Update a (key, value) pair.
        program_store.update_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key got initialized.
        assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns Some(value).
        assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

        // Ensure calling `insert_key_value` with the same key and value fails.
        assert!(program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).is_err());
        // Ensure the key is still initialized.
        assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns Some(value).
        assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

        // Ensure calling `update_key_value` with the same key and value succeeds.
        program_store.update_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
        // Ensure the key is still initialized.
        assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns Some(value).
        assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

        {
            // Prepare the same key and different value.
            let new_value = Value::from_str("123456789u128").unwrap();

            // Ensure calling `insert_key_value` with a different key and value fails.
            assert!(
                program_store.insert_key_value(&program_id, &mapping_name, key.clone(), new_value.clone()).is_err()
            );
            // Ensure the key is still initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value still returns Some(value).
            assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

            // Ensure calling `update_key_value` with a different key and value succeeds.
            program_store.update_key_value(&program_id, &mapping_name, key.clone(), new_value.clone()).unwrap();
            // Ensure the key is still initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(new_value).
            assert_eq!(new_value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

            // Ensure calling `update_key_value` with the same key and original value succeeds.
            program_store.update_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the key is still initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Ensure removing the key succeeds.
        program_store.remove_key_value(&program_id, &mapping_name, &key).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is still initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key got removed.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the mapping succeeds.
        program_store.remove_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

        // Ensure removing the program succeeds.
        program_store.remove_program(&program_id).unwrap();
        // Ensure the program ID is no longer initialized.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is still no longer initialized.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure the key is still removed.
        assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
        // Ensure the value still returns None.
        assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
    }

    #[test]
    fn test_initialize_insert_remove() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new program store.
        let program_store = ProgramMemory::open(None).unwrap();
        // Check the operations.
        check_initialize_insert_remove(&program_store, program_id, mapping_name);
    }

    #[test]
    fn test_initialize_update_remove() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new program store.
        let program_store = ProgramMemory::open(None).unwrap();
        // Check the operations.
        check_initialize_update_remove(&program_store, program_id, mapping_name);
    }

    #[test]
    fn test_remove_key_value() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new program store.
        let program_store = ProgramMemory::open(None).unwrap();
        // Ensure the program ID does not exist.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        program_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());

        // Insert the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key did not get initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

            // Insert the key and value.
            program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the program ID is still initialized.
            assert!(program_store.contains_program(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
            // Ensure the key got initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Remove the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key is still initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());

            // Remove the key-value pair.
            program_store.remove_key_value(&program_id, &mapping_name, &key).unwrap();
            // Ensure the program ID is still initialized.
            assert!(program_store.contains_program(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
            // Ensure the key is no longer initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
        }
    }

    #[test]
    fn test_remove_mapping() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new program store.
        let program_store = ProgramMemory::open(None).unwrap();
        // Ensure the program ID does not exist.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        program_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());

        // Insert the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key did not get initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

            // Insert the key and value.
            program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the program ID is still initialized.
            assert!(program_store.contains_program(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
            // Ensure the key got initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Remove the mapping.
        program_store.remove_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID is still initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());

        // Check the list of keys and values.
        for item in 0..1000 {
            // Prepare the key.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();

            // Ensure the key is no longer initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
        }
    }

    #[test]
    fn test_remove_program() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new program store.
        let program_store = ProgramMemory::open(None).unwrap();
        // Ensure the program ID does not exist.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());

        // Now, initialize the mapping.
        program_store.initialize_mapping(&program_id, &mapping_name).unwrap();
        // Ensure the program ID got initialized.
        assert!(program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name got initialized.
        assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());

        // Insert the list of keys and values.
        for item in 0..1000 {
            // Prepare the key and value.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();
            let value = Value::from_str(&format!("{item}u64")).unwrap();
            // Ensure the key did not get initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());

            // Insert the key and value.
            program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
            // Ensure the program ID is still initialized.
            assert!(program_store.contains_program(&program_id).unwrap());
            // Ensure the mapping name is still initialized.
            assert!(program_store.contains_mapping(&program_id, &mapping_name).unwrap());
            // Ensure the key got initialized.
            assert!(program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns Some(value).
            assert_eq!(value, program_store.get_value(&program_id, &mapping_name, &key).unwrap().unwrap());
        }

        // Remove the program.
        program_store.remove_program(&program_id).unwrap();
        // Ensure the program ID is no longer initialized.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name is no longer initialized.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());

        // Check the list of keys and values.
        for item in 0..1000 {
            // Prepare the key.
            let key = Plaintext::from_str(&format!("{item}field")).unwrap();

            // Ensure the key is no longer initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
        }
    }

    #[test]
    fn test_must_initialize_first() {
        // Initialize a program ID and mapping name.
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();
        let mapping_name = Identifier::from_str("account").unwrap();

        // Initialize a new program store.
        let program_store = ProgramMemory::open(None).unwrap();
        // Ensure the program ID does not exist.
        assert!(!program_store.contains_program(&program_id).unwrap());
        // Ensure the mapping name does not exist.
        assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
        // Ensure removing an un-initialized mapping fails.
        assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());

        {
            // Ensure inserting a (key, value) before initializing the mapping fails.
            let key = Plaintext::from_str("123456789field").unwrap();
            let value = Value::from_str("987654321u128").unwrap();
            assert!(program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value).is_err());

            // Ensure the program ID did not get initialized.
            assert!(!program_store.contains_program(&program_id).unwrap());
            // Ensure the mapping name did not get initialized.
            assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
            // Ensure the key did not get initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
            // Ensure removing an un-initialized key fails.
            assert!(program_store.remove_key_value(&program_id, &mapping_name, &key).is_err());
            // Ensure removing an un-initialized mapping fails.
            assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());
        }
        {
            // Ensure updating a (key, value) before initializing the mapping fails.
            let key = Plaintext::from_str("987654321field").unwrap();
            let value = Value::from_str("123456789u128").unwrap();
            assert!(program_store.update_key_value(&program_id, &mapping_name, key.clone(), value).is_err());

            // Ensure the program ID did not get initialized.
            assert!(!program_store.contains_program(&program_id).unwrap());
            // Ensure the mapping name did not get initialized.
            assert!(!program_store.contains_mapping(&program_id, &mapping_name).unwrap());
            // Ensure the key did not get initialized.
            assert!(!program_store.contains_key(&program_id, &mapping_name, &key).unwrap());
            // Ensure the value returns None.
            assert!(program_store.get_value(&program_id, &mapping_name, &key).unwrap().is_none());
            // Ensure removing an un-initialized key fails.
            assert!(program_store.remove_key_value(&program_id, &mapping_name, &key).is_err());
            // Ensure removing an un-initialized mapping fails.
            assert!(program_store.remove_mapping(&program_id, &mapping_name).is_err());
        }

        // Ensure program storage still behaves correctly after the above operations.
        check_initialize_insert_remove(&program_store, program_id, mapping_name);
        check_initialize_update_remove(&program_store, program_id, mapping_name);
    }
}
