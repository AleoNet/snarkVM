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

use crate::{helpers::memory::MemoryMap, InputStorage, InputStore, OutputStorage, OutputStore, TransitionStorage};
use console::{
    prelude::*,
    program::{Ciphertext, Identifier, Plaintext, ProgramID, Record, Value},
    types::{Field, Group},
};

/// An in-memory transition storage.
#[derive(Clone)]
pub struct TransitionMemory<N: Network> {
    /// The transition program IDs and function names.
    locator_map: MemoryMap<N::TransitionID, (ProgramID<N>, Identifier<N>)>,
    /// The transition input store.
    input_store: InputStore<N, InputMemory<N>>,
    /// The transition output store.
    output_store: OutputStore<N, OutputMemory<N>>,
    /// The transition finalize inputs.
    finalize_map: MemoryMap<N::TransitionID, Option<Vec<Value<N>>>>,
    /// The transition public keys.
    tpk_map: MemoryMap<N::TransitionID, Group<N>>,
    /// The reverse `tpk` map.
    reverse_tpk_map: MemoryMap<Group<N>, N::TransitionID>,
    /// The transition commitments.
    tcm_map: MemoryMap<N::TransitionID, Field<N>>,
    /// The reverse `tcm` map.
    reverse_tcm_map: MemoryMap<Field<N>, N::TransitionID>,
}

#[rustfmt::skip]
impl<N: Network> TransitionStorage<N> for TransitionMemory<N> {
    type LocatorMap = MemoryMap<N::TransitionID, (ProgramID<N>, Identifier<N>)>;
    type InputStorage = InputMemory<N>;
    type OutputStorage = OutputMemory<N>;
    type FinalizeMap = MemoryMap<N::TransitionID, Option<Vec<Value<N>>>>;
    type TPKMap = MemoryMap<N::TransitionID, Group<N>>;
    type ReverseTPKMap = MemoryMap<Group<N>, N::TransitionID>;
    type TCMMap = MemoryMap<N::TransitionID, Field<N>>;
    type ReverseTCMMap = MemoryMap<Field<N>, N::TransitionID>;

    /// Initializes the transition storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            locator_map: MemoryMap::default(),
            input_store: InputStore::open(dev)?,
            output_store: OutputStore::open(dev)?,
            finalize_map: MemoryMap::default(),
            tpk_map: MemoryMap::default(),
            reverse_tpk_map: MemoryMap::default(),
            tcm_map: MemoryMap::default(),
            reverse_tcm_map: MemoryMap::default(),
        })
    }

    /// Returns the transition program IDs and function names.
    fn locator_map(&self) -> &Self::LocatorMap {
        &self.locator_map
    }

    /// Returns the transition input store.
    fn input_store(&self) -> &InputStore<N, Self::InputStorage> {
        &self.input_store
    }

    /// Returns the transition output store.
    fn output_store(&self) -> &OutputStore<N, Self::OutputStorage> {
        &self.output_store
    }

    /// Returns the transition finalize inputs.
    fn finalize_map(&self) -> &Self::FinalizeMap {
        &self.finalize_map
    }

    /// Returns the transition public keys.
    fn tpk_map(&self) -> &Self::TPKMap {
        &self.tpk_map
    }

    /// Returns the reverse `tpk` map.
    fn reverse_tpk_map(&self) -> &Self::ReverseTPKMap {
        &self.reverse_tpk_map
    }

    /// Returns the transition commitments.
    fn tcm_map(&self) -> &Self::TCMMap {
        &self.tcm_map
    }

    /// Returns the reverse `tcm` map.
    fn reverse_tcm_map(&self) -> &Self::ReverseTCMMap {
        &self.reverse_tcm_map
    }
}

/// An in-memory transition input storage.
#[derive(Clone)]
pub struct InputMemory<N: Network> {
    /// The mapping of `transition ID` to `input IDs`.
    id_map: MemoryMap<N::TransitionID, Vec<Field<N>>>,
    /// The mapping of `input ID` to `transition ID`.
    reverse_id_map: MemoryMap<Field<N>, N::TransitionID>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    constant: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    public: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `ciphertext hash` to `(optional) ciphertext`.
    private: MemoryMap<Field<N>, Option<Ciphertext<N>>>,
    /// The mapping of `serial number` to `tag`.
    record: MemoryMap<Field<N>, Field<N>>,
    /// The mapping of `record tag` to `serial number`.
    record_tag: MemoryMap<Field<N>, Field<N>>,
    /// The mapping of `external hash` to `()`. Note: This is **not** the record commitment.
    external_record: MemoryMap<Field<N>, ()>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> InputStorage<N> for InputMemory<N> {
    type IDMap = MemoryMap<N::TransitionID, Vec<Field<N>>>;
    type ReverseIDMap = MemoryMap<Field<N>, N::TransitionID>;
    type ConstantMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PublicMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PrivateMap = MemoryMap<Field<N>, Option<Ciphertext<N>>>;
    type RecordMap = MemoryMap<Field<N>, Field<N>>;
    type RecordTagMap = MemoryMap<Field<N>, Field<N>>;
    type ExternalRecordMap = MemoryMap<Field<N>, ()>;

    /// Initializes the transition input storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            constant: MemoryMap::default(),
            public: MemoryMap::default(),
            private: MemoryMap::default(),
            record: MemoryMap::default(),
            record_tag: MemoryMap::default(),
            external_record: MemoryMap::default(),
            dev,
        })
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the constant map.
    fn constant_map(&self) -> &Self::ConstantMap {
        &self.constant
    }

    /// Returns the public map.
    fn public_map(&self) -> &Self::PublicMap {
        &self.public
    }

    /// Returns the private map.
    fn private_map(&self) -> &Self::PrivateMap {
        &self.private
    }

    /// Returns the record map.
    fn record_map(&self) -> &Self::RecordMap {
        &self.record
    }

    /// Returns the record tag map.
    fn record_tag_map(&self) -> &Self::RecordTagMap {
        &self.record_tag
    }

    /// Returns the external record map.
    fn external_record_map(&self) -> &Self::ExternalRecordMap {
        &self.external_record
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}

/// An in-memory transition output storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct OutputMemory<N: Network> {
    /// The mapping of `transition ID` to `output IDs`.
    id_map: MemoryMap<N::TransitionID, Vec<Field<N>>>,
    /// The mapping of `output ID` to `transition ID`.
    reverse_id_map: MemoryMap<Field<N>, N::TransitionID>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    constant: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `plaintext hash` to `(optional) plaintext`.
    public: MemoryMap<Field<N>, Option<Plaintext<N>>>,
    /// The mapping of `ciphertext hash` to `(optional) ciphertext`.
    private: MemoryMap<Field<N>, Option<Ciphertext<N>>>,
    /// The mapping of `commitment` to `(checksum, (optional) record ciphertext)`.
    record: MemoryMap<Field<N>, (Field<N>, Option<Record<N, Ciphertext<N>>>)>,
    /// The mapping of `record nonce` to `commitment`.
    record_nonce: MemoryMap<Group<N>, Field<N>>,
    /// The mapping of `external hash` to `()`. Note: This is **not** the record commitment.
    external_record: MemoryMap<Field<N>, ()>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> OutputStorage<N> for OutputMemory<N> {
    type IDMap = MemoryMap<N::TransitionID, Vec<Field<N>>>;
    type ReverseIDMap = MemoryMap<Field<N>, N::TransitionID>;
    type ConstantMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PublicMap = MemoryMap<Field<N>, Option<Plaintext<N>>>;
    type PrivateMap = MemoryMap<Field<N>, Option<Ciphertext<N>>>;
    type RecordMap = MemoryMap<Field<N>, (Field<N>, Option<Record<N, Ciphertext<N>>>)>;
    type RecordNonceMap = MemoryMap<Group<N>, Field<N>>;
    type ExternalRecordMap = MemoryMap<Field<N>, ()>;

    /// Initializes the transition output storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            id_map: Default::default(),
            reverse_id_map: Default::default(),
            constant: Default::default(),
            public: Default::default(),
            private: Default::default(),
            record: Default::default(),
            record_nonce: Default::default(),
            external_record: Default::default(),
            dev,
        })
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the constant map.
    fn constant_map(&self) -> &Self::ConstantMap {
        &self.constant
    }

    /// Returns the public map.
    fn public_map(&self) -> &Self::PublicMap {
        &self.public
    }

    /// Returns the private map.
    fn private_map(&self) -> &Self::PrivateMap {
        &self.private
    }

    /// Returns the record map.
    fn record_map(&self) -> &Self::RecordMap {
        &self.record
    }

    /// Returns the record nonce map.
    fn record_nonce_map(&self) -> &Self::RecordNonceMap {
        &self.record_nonce
    }

    /// Returns the external record map.
    fn external_record_map(&self) -> &Self::ExternalRecordMap {
        &self.external_record
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}
