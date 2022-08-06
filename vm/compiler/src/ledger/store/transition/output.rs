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
    transition::{Origin, Output},
};
use console::{
    network::prelude::*,
    program::{Ciphertext, Record},
    types::Field,
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition output storage.
pub trait OutputStorage<N: Network> {
    /// The plaintext hash and (optional) plaintext.
    type ConstantMap: for<'a> Map<'a, N::TransitionID, Output<N>>;
    /// The plaintext hash and (optional) plaintext.
    type PublicMap: for<'a> Map<'a, N::TransitionID, Output<N>>;
    /// The ciphertext hash and (optional) ciphertext.
    type PrivateMap: for<'a> Map<'a, N::TransitionID, Output<N>>;
    /// The serial number, tag, and the origin of the record.
    type RecordMap: for<'a> Map<'a, N::TransitionID, Output<N>>;
    /// The output commitment to the external record. Note: This is **not** the record commitment.
    type ExternalRecordMap: for<'a> Map<'a, N::TransitionID, Output<N>>;

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

    /// Opens the transition output store.
    fn open(&self) -> Result<OutputStore<N, Self>>
    where
        Self: Sized,
    {
        Ok(OutputStore::new(
            self.constant_map()?,
            self.public_map()?,
            self.private_map()?,
            self.record_map()?,
            self.external_record_map()?,
        ))
    }
}

/// An in-memory transition output storage.
#[derive(Clone, Default)]
pub struct OutputMemory<N: Network> {
    /// The plaintext hash and (optional) plaintext.
    constant: MemoryMap<N::TransitionID, Output<N>>,
    /// The plaintext hash and (optional) plaintext.
    public: MemoryMap<N::TransitionID, Output<N>>,
    /// The ciphertext hash and (optional) ciphertext.
    private: MemoryMap<N::TransitionID, Output<N>>,
    /// The serial number, tag, and the origin of the record.
    record: MemoryMap<N::TransitionID, Output<N>>,
    /// The output commitment to the external record. Note: This is **not** the record commitment.
    external_record: MemoryMap<N::TransitionID, Output<N>>,
}

impl<N: Network> OutputMemory<N> {
    /// Creates a new in-memory transition output storage.
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
impl<N: Network> OutputStorage<N> for OutputMemory<N> {
    type ConstantMap = MemoryMap<N::TransitionID, Output<N>>;
    type PublicMap = MemoryMap<N::TransitionID, Output<N>>;
    type PrivateMap = MemoryMap<N::TransitionID, Output<N>>;
    type RecordMap = MemoryMap<N::TransitionID, Output<N>>;
    type ExternalRecordMap = MemoryMap<N::TransitionID, Output<N>>;

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

/// A transition output storage.
pub struct OutputStore<N: Network, I: OutputStorage<N>> {
    /// The map of constant outputs.
    constant: I::ConstantMap,
    /// The map of public outputs.
    public: I::PublicMap,
    /// The map of private outputs.
    private: I::PrivateMap,
    /// The map of record outputs.
    record: I::RecordMap,
    /// The map of external record outputs.
    external_record: I::ExternalRecordMap,
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Creates a new output store.
    pub fn new(
        constant: I::ConstantMap,
        public: I::PublicMap,
        private: I::PrivateMap,
        record: I::RecordMap,
        external_record: I::ExternalRecordMap,
    ) -> Self {
        Self { constant, public, private, record, external_record }
    }

    /// Initializes a new output store from the given output storage.
    pub fn from(storage: I) -> Result<Self> {
        storage.open()
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns the output for the given `transition ID`.
    pub fn get(&self, transition_id: &N::TransitionID) -> Result<Option<Output<N>>> {
        // Load the output.
        let constant = self.constant.get(transition_id)?;
        let public = self.public.get(transition_id)?;
        let private = self.private.get(transition_id)?;
        let record = self.record.get(transition_id)?;
        let external_record = self.external_record.get(transition_id)?;

        // Retrieve the output.
        let output = match (constant, public, private, record, external_record) {
            (Some(constant), None, None, None, None) => Some(constant),
            (None, Some(public), None, None, None) => Some(public),
            (None, None, Some(private), None, None) => Some(private),
            (None, None, None, Some(record), None) => Some(record),
            (None, None, None, None, Some(external_record)) => Some(external_record),
            (None, None, None, None, None) => None,
            _ => bail!("Found multiple outputs for the same transition ID '{transition_id}'"),
        };

        // Return the output.
        match output {
            Some(Cow::Borrowed(output)) => Ok(Some(output.clone())),
            Some(Cow::Owned(output)) => Ok(Some(output)),
            None => Ok(None),
        }
    }

    /// Stores the given `(transition ID, output)` pair into storage.
    pub fn insert(&mut self, transition_id: N::TransitionID, output: Output<N>) -> Result<()> {
        match output {
            Output::Constant(..) => self.constant.insert(transition_id, output),
            Output::Public(..) => self.public.insert(transition_id, output),
            Output::Private(..) => self.private.insert(transition_id, output),
            Output::Record(..) => self.record.insert(transition_id, output),
            Output::ExternalRecord(..) => self.external_record.insert(transition_id, output),
        }
    }

    /// Removes the output for the given `transition ID`.
    pub fn remove(&mut self, transition_id: &N::TransitionID) -> Result<()> {
        self.constant.remove(transition_id)?;
        self.public.remove(transition_id)?;
        self.private.remove(transition_id)?;
        self.record.remove(transition_id)?;
        self.external_record.remove(transition_id)?;
        Ok(())
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns an iterator over the constant outputs, for all transitions.
    pub fn constant_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Output<N>>> {
        self.constant.values()
    }

    /// Returns an iterator over the constant outputs, for all transitions.
    pub fn public_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Output<N>>> {
        self.public.values()
    }

    /// Returns an iterator over the private outputs, for all transitions.
    pub fn private_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Output<N>>> {
        self.private.values()
    }

    /// Returns an iterator over the record outputs, for all transitions.
    pub fn record_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Output<N>>> {
        self.record.values()
    }

    /// Returns an iterator over the external record outputs, for all transitions.
    pub fn external_record_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Output<N>>> {
        self.external_record.values()
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.commitments().contains(commitment)
    }

    /// Returns `true` if the given checksum exists.
    pub fn contains_checksum(&self, checksum: &Field<N>) -> bool {
        self.checksums().contains(checksum)
    }

    /// Returns `true` if the given record ciphertext exists.
    pub fn contains_record_ciphertext(&self, record_ciphertext: &Record<N, Ciphertext<N>>) -> bool {
        self.record_ciphertexts().contains(record_ciphertext)
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.values().flat_map(|output| match output {
            Cow::Borrowed(Output::Record(commitment, _, _)) => CowIter::Borrowed([commitment].into_iter()),
            Cow::Owned(Output::Record(commitment, _, _)) => CowIter::Owned([commitment].into_iter()),
            _ => CowIter::None,
        })
    }

    /// Returns an iterator over the checksums, for all transition outputs that are records.
    pub fn checksums(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.values().flat_map(|output| match output {
            Cow::Borrowed(Output::Record(_, checksum, _)) => CowIter::Borrowed([checksum].into_iter()),
            Cow::Owned(Output::Record(_, checksum, _)) => CowIter::Owned([checksum].into_iter()),
            _ => CowIter::None,
        })
    }

    /// Returns an iterator over the record ciphertexts, for all transition outputs that are records.
    pub fn record_ciphertexts(&self) -> impl '_ + Iterator<Item = Cow<'_, Record<N, Ciphertext<N>>>> {
        self.record.values().flat_map(|output| match output {
            Cow::Borrowed(Output::Record(_, _, ciphertext)) => CowIter::Borrowed([ciphertext].into_iter().flatten()),
            Cow::Owned(Output::Record(_, _, ciphertext)) => CowIter::Owned([ciphertext].into_iter().flatten()),
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
        // Sample the transition outputs.
        for (transition_id, output) in crate::ledger::transition::output::test_helpers::sample_outputs() {
            // Initialize a new output store.
            let mut output_store = OutputMemory::new().open().unwrap();

            // Ensure the transition output does not exist.
            let candidate = output_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);

            // Insert the transition output.
            output_store.insert(transition_id, output.clone()).unwrap();

            // Retrieve the transition output.
            let candidate = output_store.get(&transition_id).unwrap();
            assert_eq!(Some(output.clone()), candidate);

            // Remove the transition output.
            output_store.remove(&transition_id).unwrap();

            // Retrieve the transition output.
            let candidate = output_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
