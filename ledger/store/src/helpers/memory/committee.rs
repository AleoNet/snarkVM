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

use crate::{helpers::memory::MemoryMap, CommitteeStorage};
use console::prelude::*;
use ledger_committee::Committee;

/// An in-memory committee storage.
#[derive(Clone)]
pub struct CommitteeMemory<N: Network> {
    /// The current round map.
    current_round_map: MemoryMap<u8, u64>,
    /// The round to height map.
    round_to_height_map: MemoryMap<u64, u32>,
    /// The committee map.
    committee_map: MemoryMap<u32, Committee<N>>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> CommitteeStorage<N> for CommitteeMemory<N> {
    type CurrentRoundMap = MemoryMap<u8, u64>;
    type RoundToHeightMap = MemoryMap<u64, u32>;
    type CommitteeMap = MemoryMap<u32, Committee<N>>;

    /// Initializes the committee storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            current_round_map: MemoryMap::default(),
            round_to_height_map: MemoryMap::default(),
            committee_map: MemoryMap::default(),
            dev,
        })
    }

    /// Returns the current round map.
    fn current_round_map(&self) -> &Self::CurrentRoundMap {
        &self.current_round_map
    }

    /// Returns the round to height map.
    fn round_to_height_map(&self) -> &Self::RoundToHeightMap {
        &self.round_to_height_map
    }

    /// Returns the committee map.
    fn committee_map(&self) -> &Self::CommitteeMap {
        &self.committee_map
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}
