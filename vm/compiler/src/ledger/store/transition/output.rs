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
    transition::Output,
};
use console::{
    network::prelude::*,
    program::{Ciphertext, Plaintext, Record},
    types::Field,
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition output storage.
pub trait OutputStorage<N: Network> {
    /// The mapping of `transition ID` to `output ID`.
    type IDMap: for<'a> Map<'a, N::TransitionID, Vec<Field<N>>>;
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    type ConstantMap: for<'a> Map<'a, Field<N>, Option<Plaintext<N>>>;
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    type PublicMap: for<'a> Map<'a, Field<N>, Option<Plaintext<N>>>;
    /// The mapping of `ciphertext hash` to `(optional) ciphertext`.
    type PrivateMap: for<'a> Map<'a, Field<N>, Option<Ciphertext<N>>>;
    /// The mapping of `commitment` to `(checksum, (optional) record ciphertext)`.
    type RecordMap: for<'a> Map<'a, Field<N>, (Field<N>, Option<Record<N, Ciphertext<N>>>)>;
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

    /// Opens the transition output store.
    fn open(&self) -> Result<OutputStore<N, Self>>
    where
        Self: Sized,
    {
        Ok(OutputStore::new(
            self.id_map()?,
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
    /// The mapping of `transition ID` to `output ID`.
    id_map: MemoryMap<N::TransitionID, Vec<Field<N>>>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    constant: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    public: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `ciphertext hash` to `(optional) ciphertext`.
    private: MemoryMap<Field<N>, Option<Ciphertext<N>>>,
    /// The mapping of `commitment` to `(checksum, (optional) record ciphertext)`.
    record: MemoryMap<Field<N>, (Field<N>, Option<Record<N, Ciphertext<N>>>)>,
    /// The mapping of `external commitment` to `()`. Note: This is **not** the record commitment.
    external_record: MemoryMap<Field<N>, ()>,
}

impl<N: Network> OutputMemory<N> {
    /// Creates a new in-memory transition output storage.
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
impl<N: Network> OutputStorage<N> for OutputMemory<N> {
    type IDMap = MemoryMap<N::TransitionID, Vec<Field<N>>>;
    type ConstantMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PublicMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PrivateMap = MemoryMap<Field<N>, Option<Ciphertext<N>>>;
    type RecordMap = MemoryMap<Field<N>, (Field<N>, Option<Record<N, Ciphertext<N>>>)>;
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

/// A transition output storage.
pub struct OutputStore<N: Network, I: OutputStorage<N>> {
    /// The map of `transition ID` to `[output ID]`.
    output_ids: I::IDMap,
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
    /// Initializes a new output store from the given maps.
    pub fn new(
        output_ids: I::IDMap,
        constant: I::ConstantMap,
        public: I::PublicMap,
        private: I::PrivateMap,
        record: I::RecordMap,
        external_record: I::ExternalRecordMap,
    ) -> Self {
        Self { output_ids, constant, public, private, record, external_record }
    }

    /// Initializes a new output store from the given output storage.
    pub fn from(storage: I) -> Result<Self> {
        storage.open()
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns the output IDs for the given `transition ID`.
    pub fn get_ids(&self, transition_id: &N::TransitionID) -> Result<Vec<Field<N>>> {
        // Retrieve the output IDs.
        match self.output_ids.get(&transition_id)? {
            Some(Cow::Borrowed(outputs)) => Ok(outputs.to_vec()),
            Some(Cow::Owned(outputs)) => Ok(outputs),
            None => Ok(vec![]),
        }
    }

    /// Returns the output for the given `transition ID`.
    pub fn get(&self, transition_id: &N::TransitionID) -> Result<Vec<Output<N>>> {
        // Constructs the output given the output ID and output value.
        macro_rules! into_output {
            (Output::Record($output_id:ident, $output:expr)) => {
                match $output {
                    Cow::Borrowed((checksum, opt_record)) => Output::Record($output_id, *checksum, opt_record.clone()),
                    Cow::Owned((checksum, opt_record)) => Output::Record($output_id, checksum, opt_record),
                }
            };
            (Output::$Variant:ident($output_id:ident, $output:expr)) => {
                match $output {
                    Cow::Borrowed(output) => Output::$Variant($output_id, output.clone()),
                    Cow::Owned(output) => Output::$Variant($output_id, output),
                }
            };
        }

        // A helper function to construct the output given the output ID.
        let construct_output = |output_id| {
            let constant = self.constant.get(&output_id)?;
            let public = self.public.get(&output_id)?;
            let private = self.private.get(&output_id)?;
            let record = self.record.get(&output_id)?;
            let external_record = self.external_record.get(&output_id)?;

            // Retrieve the output.
            let output = match (constant, public, private, record, external_record) {
                (Some(constant), None, None, None, None) => into_output!(Output::Constant(output_id, constant)),
                (None, Some(public), None, None, None) => into_output!(Output::Public(output_id, public)),
                (None, None, Some(private), None, None) => into_output!(Output::Private(output_id, private)),
                (None, None, None, Some(record), None) => into_output!(Output::Record(output_id, record)),
                (None, None, None, None, Some(_)) => Output::ExternalRecord(output_id),
                (None, None, None, None, None) => bail!("Missing output '{output_id}' in transition '{transition_id}'"),
                _ => bail!("Found multiple outputs for the output ID '{output_id}' in transition '{transition_id}'"),
            };

            Ok(output)
        };

        // Retrieve the output IDs.
        match self.output_ids.get(&transition_id)? {
            Some(Cow::Borrowed(ids)) => ids.iter().map(|output_id| construct_output(*output_id)).collect(),
            Some(Cow::Owned(ids)) => ids.iter().map(|output_id| construct_output(*output_id)).collect(),
            None => Ok(vec![]),
        }
    }

    /// Stores the given `(transition ID, output)` pair into storage.
    pub fn insert(&mut self, transition_id: N::TransitionID, outputs: &[Output<N>]) -> Result<()> {
        // Store the output IDs.
        self.output_ids.insert(transition_id, outputs.iter().map(Output::id).cloned().collect())?;

        // Store the outputs.
        for output in outputs {
            match output {
                Output::Constant(output_id, constant) => self.constant.insert(*output_id, constant.clone())?,
                Output::Public(output_id, public) => self.public.insert(*output_id, public.clone())?,
                Output::Private(output_id, private) => self.private.insert(*output_id, private.clone())?,
                Output::Record(commitment, checksum, optional_record) => {
                    self.record.insert(*commitment, (*checksum, optional_record.clone()))?
                }
                Output::ExternalRecord(output_id) => self.external_record.insert(*output_id, ())?,
            }
        }
        Ok(())
    }

    /// Removes the output for the given `transition ID`.
    pub fn remove(&mut self, transition_id: &N::TransitionID) -> Result<()> {
        // A helper function to remove the output given the output ID.
        let mut remove_output = |output_id| {
            self.constant.remove(output_id)?;
            self.public.remove(output_id)?;
            self.private.remove(output_id)?;
            self.record.remove(output_id)?;
            self.external_record.remove(output_id)?;
            Ok::<_, Error>(())
        };

        // Remove the outputs.
        match self.output_ids.get(&transition_id)? {
            Some(Cow::Borrowed(ids)) => ids.iter().try_for_each(|output_id| remove_output(output_id))?,
            Some(Cow::Owned(ids)) => ids.iter().try_for_each(|output_id| remove_output(output_id))?,
            None => return Ok(()),
        };

        // Remove the output IDs.
        self.output_ids.remove(&transition_id)?;
        Ok(())
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns an iterator over the constant output IDs, for all transition outputs that are constant.
    pub fn constant_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.constant.keys()
    }

    /// Returns an iterator over the public output IDs, for all transition outputs that are public.
    pub fn public_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.public.keys()
    }

    /// Returns an iterator over the private output IDs, for all transition outputs that are private.
    pub fn private_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.private.keys()
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.keys()
    }

    /// Returns an iterator over the external record output IDs, for all transition outputs that are external records.
    pub fn external_record_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.private.keys()
    }
}

impl<N: Network, I: OutputStorage<N>> OutputStore<N, I> {
    /// Returns an iterator over the constant outputs, for all transitions.
    pub fn constant_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.constant.values().flat_map(|output| match output {
            Cow::Borrowed(Some(output)) => Some(Cow::Borrowed(output)),
            Cow::Owned(Some(output)) => Some(Cow::Owned(output)),
            _ => None,
        })
    }

    /// Returns an iterator over the constant outputs, for all transitions.
    pub fn public_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.public.values().flat_map(|output| match output {
            Cow::Borrowed(Some(output)) => Some(Cow::Borrowed(output)),
            Cow::Owned(Some(output)) => Some(Cow::Owned(output)),
            _ => None,
        })
    }

    /// Returns an iterator over the private outputs, for all transitions.
    pub fn private_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Ciphertext<N>>> {
        self.private.values().flat_map(|output| match output {
            Cow::Borrowed(Some(output)) => Some(Cow::Borrowed(output)),
            Cow::Owned(Some(output)) => Some(Cow::Owned(output)),
            _ => None,
        })
    }

    /// Returns an iterator over the checksums, for all transition outputs that are records.
    pub fn checksums(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.record.values().map(|output| match output {
            Cow::Borrowed((checksum, _)) => Cow::Borrowed(checksum),
            Cow::Owned((checksum, _)) => Cow::Owned(checksum),
        })
    }

    /// Returns an iterator over the records, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = Cow<'_, Record<N, Ciphertext<N>>>> {
        self.record.values().flat_map(|output| match output {
            Cow::Borrowed((_, Some(record))) => Some(Cow::Borrowed(record)),
            Cow::Owned((_, Some(record))) => Some(Cow::Owned(record)),
            _ => None,
        })
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

    /// Returns `true` if the given record exists.
    pub fn contains_record(&self, record: &Record<N, Ciphertext<N>>) -> bool {
        self.records().contains(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        // Sample the transition outputs.
        for (transition_id, output) in crate::ledger::transition::output::test_helpers::sample_outputs() {
            // Initialize a new output store.
            let mut output_store = OutputMemory::new().open().unwrap();

            // Ensure the transition output does not exist.
            let candidate = output_store.get(&transition_id).unwrap();
            assert!(candidate.is_empty());

            // Insert the transition output.
            output_store.insert(transition_id, &[output.clone()]).unwrap();

            // Retrieve the transition output.
            let candidate = output_store.get(&transition_id).unwrap();
            assert_eq!(vec![output.clone()], candidate);

            // Remove the transition output.
            output_store.remove(&transition_id).unwrap();

            // Retrieve the transition output.
            let candidate = output_store.get(&transition_id).unwrap();
            assert!(candidate.is_empty());
        }
    }
}
