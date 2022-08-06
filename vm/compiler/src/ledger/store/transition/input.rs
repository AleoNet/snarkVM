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

use crate::ledger::{
    map::{memory_map::MemoryMap, Map, MapReader},
    store::CowIter,
    transition::{Input, Origin},
};
use console::{network::prelude::*, types::Field};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition input storage.
pub trait InputStorage<N: Network> {
    /// The plaintext hash and (optional) plaintext.
    type ConstantMap: for<'a> Map<'a, N::TransitionID, Input<N>>;
    /// The plaintext hash and (optional) plaintext.
    type PublicMap: for<'a> Map<'a, N::TransitionID, Input<N>>;
    /// The ciphertext hash and (optional) ciphertext.
    type PrivateMap: for<'a> Map<'a, N::TransitionID, Input<N>>;
    /// The serial number, tag, and the origin of the record.
    type RecordMap: for<'a> Map<'a, N::TransitionID, Input<N>>;
    /// The input commitment to the external record. Note: This is **not** the record commitment.
    type ExternalRecordMap: for<'a> Map<'a, N::TransitionID, Input<N>>;

    /// Returns the constant map.
    fn constant_map(&self) -> Result<Self::ConstantMap>;
    /// Returns the public map.
    fn public_map(&self) -> Result<Self::PublicMap>;
    /// Returns the private map.
    fn private_map(&self) -> Result<Self::PrivateMap>;
    /// Returns the record map.
    fn record_map(&self) -> Result<Self::RecordMap>;
    /// Returns the external record map.
    fn external_record_map(&self) -> Result<Self::ExternalRecordMap>;

    /// Opens the transition input store.
    fn open(&self) -> Result<InputStore<N, Self>>
    where
        Self: Sized,
    {
        Ok(InputStore::new(
            self.constant_map()?,
            self.public_map()?,
            self.private_map()?,
            self.record_map()?,
            self.external_record_map()?,
        ))
    }
}

/// An in-memory transition input storage.
#[derive(Clone, Default)]
pub struct InputMemory<N: Network> {
    /// The plaintext hash and (optional) plaintext.
    constant: MemoryMap<N::TransitionID, Input<N>>,
    /// The plaintext hash and (optional) plaintext.
    public: MemoryMap<N::TransitionID, Input<N>>,
    /// The ciphertext hash and (optional) ciphertext.
    private: MemoryMap<N::TransitionID, Input<N>>,
    /// The serial number, tag, and the origin of the record.
    record: MemoryMap<N::TransitionID, Input<N>>,
    /// The input commitment to the external record. Note: This is **not** the record commitment.
    external_record: MemoryMap<N::TransitionID, Input<N>>,
}

impl<N: Network> InputMemory<N> {
    /// Creates a new in-memory transition input storage.
    pub fn new() -> Self {
        Self {
            constant: MemoryMap::default(),
            public: MemoryMap::default(),
            private: MemoryMap::default(),
            record: MemoryMap::default(),
            external_record: MemoryMap::default(),
        }
    }
}

#[rustfmt::skip]
impl<N: Network> InputStorage<N> for InputMemory<N> {
    type ConstantMap = MemoryMap<N::TransitionID, Input<N>>;
    type PublicMap = MemoryMap<N::TransitionID, Input<N>>;
    type PrivateMap = MemoryMap<N::TransitionID, Input<N>>;
    type RecordMap = MemoryMap<N::TransitionID, Input<N>>;
    type ExternalRecordMap = MemoryMap<N::TransitionID, Input<N>>;

    /// Returns the constant map.
    fn constant_map(&self) -> Result<Self::ConstantMap> {
        Ok(self.constant.clone())
    }

    /// Returns the public map.
    fn public_map(&self) -> Result<Self::PublicMap> {
        Ok(self.public.clone())
    }

    /// Returns the private map.
    fn private_map(&self) -> Result<Self::PrivateMap> {
        Ok(self.private.clone())
    }

    /// Returns the record map.
    fn record_map(&self) -> Result<Self::RecordMap> {
        Ok(self.record.clone())
    }

    /// Returns the external record map.
    fn external_record_map(&self) -> Result<Self::ExternalRecordMap> {
        Ok(self.external_record.clone())
    }
}

/// A transition input storage.
pub struct InputStore<N: Network, I: InputStorage<N>> {
    /// The map of constant inputs.
    constant: I::ConstantMap,
    /// The map of public inputs.
    public: I::PublicMap,
    /// The map of private inputs.
    private: I::PrivateMap,
    /// The map of record inputs.
    record: I::RecordMap,
    /// The map of external record inputs.
    external_record: I::ExternalRecordMap,
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Creates a new input store.
    pub fn new(
        constant: I::ConstantMap,
        public: I::PublicMap,
        private: I::PrivateMap,
        record: I::RecordMap,
        external_record: I::ExternalRecordMap,
    ) -> Self {
        Self { constant, public, private, record, external_record }
    }

    /// Initializes a new input store from the given input storage.
    pub fn from(storage: I) -> Result<Self> {
        storage.open()
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns the input for the given `transition ID`.
    pub fn get(&self, transition_id: &N::TransitionID) -> Result<Option<Input<N>>> {
        // Load the input.
        let constant = self.constant.get(transition_id)?;
        let public = self.public.get(transition_id)?;
        let private = self.private.get(transition_id)?;
        let record = self.record.get(transition_id)?;
        let external_record = self.external_record.get(transition_id)?;

        // Retrieve the input.
        let input = match (constant, public, private, record, external_record) {
            (Some(constant), None, None, None, None) => Some(constant),
            (None, Some(public), None, None, None) => Some(public),
            (None, None, Some(private), None, None) => Some(private),
            (None, None, None, Some(record), None) => Some(record),
            (None, None, None, None, Some(external_record)) => Some(external_record),
            (None, None, None, None, None) => None,
            _ => bail!("Found multiple inputs for the same transition ID '{transition_id}'"),
        };

        // Return the input.
        match input {
            Some(Cow::Borrowed(input)) => Ok(Some(input.clone())),
            Some(Cow::Owned(input)) => Ok(Some(input)),
            None => Ok(None),
        }
    }

    /// Stores the given `(transition ID, input)` pair into storage.
    pub fn insert(&mut self, transition_id: N::TransitionID, input: Input<N>) -> Result<()> {
        match input {
            Input::Constant(..) => self.constant.insert(transition_id, input),
            Input::Public(..) => self.public.insert(transition_id, input),
            Input::Private(..) => self.private.insert(transition_id, input),
            Input::Record(..) => self.record.insert(transition_id, input),
            Input::ExternalRecord(..) => self.external_record.insert(transition_id, input),
        }
    }

    /// Removes the input for the given `transition ID`.
    pub fn remove(&mut self, transition_id: &N::TransitionID) -> Result<()> {
        self.constant.remove(transition_id)?;
        self.public.remove(transition_id)?;
        self.private.remove(transition_id)?;
        self.record.remove(transition_id)?;
        self.external_record.remove(transition_id)?;
        Ok(())
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns an iterator over the constant inputs, for all transitions.
    pub fn constant_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Input<N>>> {
        self.constant.values()
    }

    /// Returns an iterator over the constant inputs, for all transitions.
    pub fn public_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Input<N>>> {
        self.public.values()
    }

    /// Returns an iterator over the private inputs, for all transitions.
    pub fn private_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Input<N>>> {
        self.private.values()
    }

    /// Returns an iterator over the record inputs, for all transitions.
    pub fn record_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Input<N>>> {
        self.record.values()
    }

    /// Returns an iterator over the external record inputs, for all transitions.
    pub fn external_record_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Input<N>>> {
        self.external_record.values()
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns `true` if the given origin exists.
    pub fn contains_origin(&self, origin: &Origin<N>) -> bool {
        self.origins().contains(origin)
    }

    /// Returns `true` if the given tag exists.
    pub fn contains_tag(&self, tag: &Field<N>) -> bool {
        self.tags().contains(tag)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.serial_numbers().contains(serial_number)
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns an iterator over the origins, for all transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = Cow<'_, Origin<N>>> {
        self.record.values().flat_map(|input| match input {
            Cow::Borrowed(Input::Record(_, _, origin)) => CowIter::Borrowed([origin].into_iter()),
            Cow::Owned(Input::Record(_, _, origin)) => CowIter::Owned([origin].into_iter()),
            _ => CowIter::None,
        })
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.values().flat_map(|input| match input {
            Cow::Borrowed(Input::Record(_, tag, _)) => CowIter::Borrowed([tag].into_iter()),
            Cow::Owned(Input::Record(_, tag, _)) => CowIter::Owned([tag].into_iter()),
            _ => CowIter::None,
        })
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.values().flat_map(|input| match input {
            Cow::Borrowed(Input::Record(serial_number, _, _)) => CowIter::Borrowed([serial_number].into_iter()),
            Cow::Owned(Input::Record(serial_number, _, _)) => CowIter::Owned([serial_number].into_iter()),
            _ => CowIter::None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ledger::Transition;
    use console::{
        network::Testnet3,
        program::{Ciphertext, Literal, Plaintext},
    };

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_insert_get_remove() {
        // Sample the transition inputs.
        for (transition_id, input) in crate::ledger::transition::input::test_helpers::sample_inputs() {
            // Initialize a new input store.
            let mut input_store = InputMemory::new().open().unwrap();

            // Ensure the transition input does not exist.
            let candidate = input_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);

            // Insert the transition input.
            input_store.insert(transition_id, input.clone()).unwrap();

            // Retrieve the transition input.
            let candidate = input_store.get(&transition_id).unwrap();
            assert_eq!(Some(input.clone()), candidate);

            // Remove the transition input.
            input_store.remove(&transition_id).unwrap();

            // Retrieve the transition input.
            let candidate = input_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
