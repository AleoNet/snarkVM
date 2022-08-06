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

mod input;
pub use input::*;

mod output;
pub use output::*;

use crate::{
    ledger::{
        map::{memory_map::MemoryMap, Map, MapRead},
        Transition,
    },
    snark::Proof,
};
use console::{
    network::prelude::*,
    program::{Identifier, ProgramID},
    types::{Field, Group},
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition input storage.
pub trait TransitionStorage<N: Network> {
    /// The transition program IDs and function names.
    type LocatorMap: for<'a> Map<'a, N::TransitionID, (ProgramID<N>, Identifier<N>)>;
    /// The transition inputs.
    type InputStorage: InputStorage<N>;
    /// The transition outputs.
    type OutputStorage: OutputStorage<N>;
    /// The transition proofs.
    type ProofMap: for<'a> Map<'a, N::TransitionID, Proof<N>>;
    /// The transition public keys.
    type TPKMap: for<'a> Map<'a, N::TransitionID, Group<N>>;
    /// The transition commitments.
    type TCMMap: for<'a> Map<'a, N::TransitionID, Field<N>>;
    /// The transition fees.
    type FeeMap: for<'a> Map<'a, N::TransitionID, i64>;

    /// Returns the transition program IDs and function names.
    fn locator_map(&self) -> &Self::LocatorMap;
    /// Returns the transition input store.
    fn input_store(&self) -> &InputStore<N, Self::InputStorage>;
    /// Returns the transition output store.
    fn output_store(&self) -> &OutputStore<N, Self::OutputStorage>;
    /// Returns the transition proofs.
    fn proof_map(&self) -> &Self::ProofMap;
    /// Returns the transition public keys.
    fn tpk_map(&self) -> &Self::TPKMap;
    /// Returns the transition commitments.
    fn tcm_map(&self) -> &Self::TCMMap;
    /// Returns the transition fees.
    fn fee_map(&self) -> &Self::FeeMap;
}

/// An in-memory transition input storage.
#[derive(Clone)]
pub struct TransitionMemory<N: Network> {
    /// The transition program IDs and function names.
    locator_map: MemoryMap<N::TransitionID, (ProgramID<N>, Identifier<N>)>,
    /// The transition input store.
    input_store: InputStore<N, InputMemory<N>>,
    /// The transition output store.
    output_store: OutputStore<N, OutputMemory<N>>,
    /// The transition proofs.
    proof_map: MemoryMap<N::TransitionID, Proof<N>>,
    /// The transition public keys.
    tpk_map: MemoryMap<N::TransitionID, Group<N>>,
    /// The transition commitments.
    tcm_map: MemoryMap<N::TransitionID, Field<N>>,
    /// The transition fees.
    fee_map: MemoryMap<N::TransitionID, i64>,
}

impl<N: Network> TransitionMemory<N> {
    /// Creates a new in-memory transition storage.
    pub fn new() -> Self {
        Self {
            locator_map: MemoryMap::default(),
            input_store: InputStore::new(InputMemory::new()),
            output_store: OutputStore::new(OutputMemory::new()),
            proof_map: MemoryMap::default(),
            tpk_map: MemoryMap::default(),
            tcm_map: MemoryMap::default(),
            fee_map: MemoryMap::default(),
        }
    }
}

#[rustfmt::skip]
impl<N: Network> TransitionStorage<N> for TransitionMemory<N> {
    type LocatorMap = MemoryMap<N::TransitionID, (ProgramID<N>, Identifier<N>)>;
    type InputStorage = InputMemory<N>;
    type OutputStorage = OutputMemory<N>;
    type ProofMap = MemoryMap<N::TransitionID, Proof<N>>;
    type TPKMap = MemoryMap<N::TransitionID, Group<N>>;
    type TCMMap = MemoryMap<N::TransitionID, Field<N>>;
    type FeeMap = MemoryMap<N::TransitionID, i64>;

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

    /// Returns the transition proofs.
    fn proof_map(&self) -> &Self::ProofMap {
        &self.proof_map
    }

    /// Returns the transition public keys.
    fn tpk_map(&self) -> &Self::TPKMap {
        &self.tpk_map
    }

    /// Returns the transition commitments.
    fn tcm_map(&self) -> &Self::TCMMap {
        &self.tcm_map
    }

    /// Returns the transition fees.
    fn fee_map(&self) -> &Self::FeeMap {
        &self.fee_map
    }
}

/// The transition store.
#[derive(Clone)]
pub struct TransitionStore<N: Network, T: TransitionStorage<N>> {
    /// The map of transition program IDs and function names.
    locator: T::LocatorMap,
    /// The map of transition inputs.
    inputs: InputStore<N, T::InputStorage>,
    /// The map of transition outputs.
    outputs: OutputStore<N, T::OutputStorage>,
    /// The map of transition proofs.
    proof: T::ProofMap,
    /// The map of transition public keys.
    tpk: T::TPKMap,
    /// The map of transition commitments.
    tcm: T::TCMMap,
    /// The map of transition fees.
    fee: T::FeeMap,
    /// The transition storage.
    storage: T,
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Initializes a new transition store.
    pub fn new(storage: T) -> Self {
        Self {
            locator: storage.locator_map().clone(),
            inputs: (*storage.input_store()).clone(),
            outputs: (*storage.output_store()).clone(),
            proof: storage.proof_map().clone(),
            tpk: storage.tpk_map().clone(),
            tcm: storage.tcm_map().clone(),
            fee: storage.fee_map().clone(),
            storage,
        }
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    // /// Returns the transition for the given `transition ID`.
    // pub fn get(&self, transition_id: &N::TransitionID) -> Result<Option<Transition<N>>> {
    //     // Retrieve the program ID and function name.
    //     let (program_id, function_name) = self
    //         .locator
    //         .get(transition_id)?
    //         .ok_or_else(|| anyhow!("Missing the program ID and function name for transition '{transition}'"))?;
    //     // Retrieve the inputs.
    //     let inputs = self.inputs.get(transition_id)?;
    // }

    //     /// Stores the given `(transition ID, transition)` pair into storage.
    //     pub fn insert(&mut self, transition_id: N::TransitionID, transition: Transition<N>) -> Result<()> {
    //     }
    //
    //     /// Removes the input for the given `transition ID`.
    //     pub fn remove(&mut self, transition_id: &N::TransitionID) -> Result<()> {
    //
    //         Ok(())
    //     }
}
