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
    transition::{Input, Origin},
};
use console::{
    network::prelude::*,
    program::{Ciphertext, Plaintext},
    types::Field,
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition input storage.
pub trait InputStorage<N: Network> {
    /// The mapping of `transition ID` to `input ID`.
    type IDMap: for<'a> Map<'a, N::TransitionID, Vec<Field<N>>>;
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    type ConstantMap: for<'a> Map<'a, Field<N>, Option<Plaintext<N>>>;
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    type PublicMap: for<'a> Map<'a, Field<N>, Option<Plaintext<N>>>;
    /// The mapping of `ciphertext hash` to `(optional) ciphertext`.
    type PrivateMap: for<'a> Map<'a, Field<N>, Option<Ciphertext<N>>>;
    /// The mapping of `serial number` to `(tag, origin)`.
    type RecordMap: for<'a> Map<'a, Field<N>, (Field<N>, Origin<N>)>;
    /// The mapping of `external commitment` to `()`. Note: This is **not** the record commitment.
    type ExternalRecordMap: for<'a> Map<'a, Field<N>, ()>;

    /// Returns the ID map.
    fn id_map(&self) -> Result<Self::IDMap>;
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
            self.id_map()?,
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
    /// The mapping of `transition ID` to `input ID`.
    id_map: MemoryMap<N::TransitionID, Vec<Field<N>>>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    constant: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    public: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `ciphertext hash` to `(optional) ciphertext`.
    private: MemoryMap<Field<N>, Option<Ciphertext<N>>>,
    /// The mapping of `serial number` to `(tag, origin)`.
    record: MemoryMap<Field<N>, (Field<N>, Origin<N>)>,
    /// The mapping of `external commitment` to `()`. Note: This is **not** the record commitment.
    external_record: MemoryMap<Field<N>, ()>,
}

impl<N: Network> InputMemory<N> {
    /// Creates a new in-memory transition input storage.
    pub fn new() -> Self {
        Self {
            id_map: MemoryMap::default(),
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
    type IDMap = MemoryMap<N::TransitionID, Vec<Field<N>>>;
    type ConstantMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PublicMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PrivateMap = MemoryMap<Field<N>, Option<Ciphertext<N>>>;
    type RecordMap = MemoryMap<Field<N>, (Field<N>, Origin<N>)>;
    type ExternalRecordMap = MemoryMap<Field<N>, ()>;

    /// Returns the ID map.
    fn id_map(&self) -> Result<Self::IDMap> {
        Ok(self.id_map.clone())
    }

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
    /// The map of `transition ID` to `[input ID]`.
    input_ids: I::IDMap,
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
    /// Initializes a new input store from the given maps.
    pub fn new(
        input_ids: I::IDMap,
        constant: I::ConstantMap,
        public: I::PublicMap,
        private: I::PrivateMap,
        record: I::RecordMap,
        external_record: I::ExternalRecordMap,
    ) -> Self {
        Self { input_ids, constant, public, private, record, external_record }
    }

    /// Initializes a new input store from the given input storage.
    pub fn from(storage: I) -> Result<Self> {
        storage.open()
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns the input IDs for the given `transition ID`.
    pub fn get_ids(&self, transition_id: &N::TransitionID) -> Result<Vec<Field<N>>> {
        // Retrieve the input IDs.
        match self.input_ids.get(&transition_id)? {
            Some(Cow::Borrowed(inputs)) => Ok(inputs.to_vec()),
            Some(Cow::Owned(inputs)) => Ok(inputs),
            None => Ok(vec![]),
        }
    }

    /// Returns the input for the given `transition ID`.
    pub fn get(&self, transition_id: &N::TransitionID) -> Result<Vec<Input<N>>> {
        // Constructs the input given the input ID and input value.
        macro_rules! into_input {
            (Input::Record($input_id:ident, $input:expr)) => {
                match $input {
                    Cow::Borrowed((tag, origin)) => Input::Record($input_id, *tag, origin.clone()),
                    Cow::Owned((tag, origin)) => Input::Record($input_id, tag, origin),
                }
            };
            (Input::$Variant:ident($input_id:ident, $input:expr)) => {
                match $input {
                    Cow::Borrowed(input) => Input::$Variant($input_id, input.clone()),
                    Cow::Owned(input) => Input::$Variant($input_id, input),
                }
            };
        }

        // A helper function to construct the input given the input ID.
        let construct_input = |input_id| {
            let constant = self.constant.get(&input_id)?;
            let public = self.public.get(&input_id)?;
            let private = self.private.get(&input_id)?;
            let record = self.record.get(&input_id)?;
            let external_record = self.external_record.get(&input_id)?;

            // Retrieve the input.
            let input = match (constant, public, private, record, external_record) {
                (Some(constant), None, None, None, None) => into_input!(Input::Constant(input_id, constant)),
                (None, Some(public), None, None, None) => into_input!(Input::Public(input_id, public)),
                (None, None, Some(private), None, None) => into_input!(Input::Private(input_id, private)),
                (None, None, None, Some(record), None) => into_input!(Input::Record(input_id, record)),
                (None, None, None, None, Some(_)) => Input::ExternalRecord(input_id),
                (None, None, None, None, None) => bail!("Missing input '{input_id}' in transition '{transition_id}'"),
                _ => bail!("Found multiple inputs for the input ID '{input_id}' in transition '{transition_id}'"),
            };

            Ok(input)
        };

        // Retrieve the input IDs.
        match self.input_ids.get(&transition_id)? {
            Some(Cow::Borrowed(ids)) => ids.iter().map(|input_id| construct_input(*input_id)).collect(),
            Some(Cow::Owned(ids)) => ids.iter().map(|input_id| construct_input(*input_id)).collect(),
            None => Ok(vec![]),
        }
    }

    /// Stores the given `(transition ID, input)` pair into storage.
    pub fn insert(&mut self, transition_id: N::TransitionID, inputs: &[Input<N>]) -> Result<()> {
        // Store the input IDs.
        self.input_ids.insert(transition_id, inputs.iter().map(Input::id).cloned().collect())?;

        // Store the inputs.
        for input in inputs {
            match input {
                Input::Constant(input_id, constant) => self.constant.insert(*input_id, constant.clone())?,
                Input::Public(input_id, public) => self.public.insert(*input_id, public.clone())?,
                Input::Private(input_id, private) => self.private.insert(*input_id, private.clone())?,
                Input::Record(serial_number, tag, origin) => {
                    self.record.insert(*serial_number, (*tag, origin.clone()))?
                }
                Input::ExternalRecord(input_id) => self.external_record.insert(*input_id, ())?,
            }
        }
        Ok(())
    }

    /// Removes the input for the given `transition ID`.
    pub fn remove(&mut self, transition_id: &N::TransitionID) -> Result<()> {
        // A helper function to remove the input given the input ID.
        let mut remove_input = |input_id| {
            self.constant.remove(input_id)?;
            self.public.remove(input_id)?;
            self.private.remove(input_id)?;
            self.record.remove(input_id)?;
            self.external_record.remove(input_id)?;
            Ok::<_, Error>(())
        };

        // Remove the inputs.
        match self.input_ids.get(&transition_id)? {
            Some(Cow::Borrowed(ids)) => ids.iter().try_for_each(|input_id| remove_input(input_id))?,
            Some(Cow::Owned(ids)) => ids.iter().try_for_each(|input_id| remove_input(input_id))?,
            None => return Ok(()),
        };

        // Remove the input IDs.
        self.input_ids.remove(&transition_id)?;
        Ok(())
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns an iterator over the constant input IDs, for all transition inputs that are constant.
    pub fn constant_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.constant.keys()
    }

    /// Returns an iterator over the public input IDs, for all transition inputs that are public.
    pub fn public_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.public.keys()
    }

    /// Returns an iterator over the private input IDs, for all transition inputs that are private.
    pub fn private_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.private.keys()
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.keys()
    }

    /// Returns an iterator over the external record input IDs, for all transition inputs that are external records.
    pub fn external_record_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.private.keys()
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns an iterator over the constant inputs, for all transitions.
    pub fn constant_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.constant.values().flat_map(|input| match input {
            Cow::Borrowed(Some(input)) => Some(Cow::Borrowed(input)),
            Cow::Owned(Some(input)) => Some(Cow::Owned(input)),
            _ => None,
        })
    }

    /// Returns an iterator over the constant inputs, for all transitions.
    pub fn public_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.public.values().flat_map(|input| match input {
            Cow::Borrowed(Some(input)) => Some(Cow::Borrowed(input)),
            Cow::Owned(Some(input)) => Some(Cow::Owned(input)),
            _ => None,
        })
    }

    /// Returns an iterator over the private inputs, for all transitions.
    pub fn private_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Ciphertext<N>>> {
        self.private.values().flat_map(|input| match input {
            Cow::Borrowed(Some(input)) => Some(Cow::Borrowed(input)),
            Cow::Owned(Some(input)) => Some(Cow::Owned(input)),
            _ => None,
        })
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.values().map(|input| match input {
            Cow::Borrowed((tag, _)) => Cow::Borrowed(tag),
            Cow::Owned((tag, _)) => Cow::Owned(tag),
        })
    }

    /// Returns an iterator over the origins, for all transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = Cow<'_, Origin<N>>> {
        self.record.values().map(|input| match input {
            Cow::Borrowed((_, origin)) => Cow::Borrowed(origin),
            Cow::Owned((_, origin)) => Cow::Owned(origin),
        })
    }
}

impl<N: Network, I: InputStorage<N>> InputStore<N, I> {
    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.serial_numbers().contains(serial_number)
    }

    /// Returns `true` if the given tag exists.
    pub fn contains_tag(&self, tag: &Field<N>) -> bool {
        self.tags().contains(tag)
    }

    /// Returns `true` if the given origin exists.
    pub fn contains_origin(&self, origin: &Origin<N>) -> bool {
        self.origins().contains(origin)
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
            assert!(candidate.is_empty());

            // Insert the transition input.
            input_store.insert(transition_id, &[input.clone()]).unwrap();

            // Retrieve the transition input.
            let candidate = input_store.get(&transition_id).unwrap();
            assert_eq!(vec![input.clone()], candidate);

            // Remove the transition input.
            input_store.remove(&transition_id).unwrap();

            // Retrieve the transition input.
            let candidate = input_store.get(&transition_id).unwrap();
            assert!(candidate.is_empty());
        }
    }
}
