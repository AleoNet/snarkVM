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
        map::{memory_map::MemoryMap, Map, MapReader},
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
    type InputMap: InputStorage<N>;
    /// The transition outputs.
    type OutputMap: OutputStorage<N>;
    /// The transition proofs.
    type ProofMap: for<'a> Map<'a, N::TransitionID, Proof<N>>;
    /// The transition public keys.
    type TPKMap: for<'a> Map<'a, N::TransitionID, Group<N>>;
    /// The transition commitments.
    type TCMMap: for<'a> Map<'a, N::TransitionID, Field<N>>;
    /// The transition fees.
    type FeeMap: for<'a> Map<'a, N::TransitionID, i64>;

    /// Returns the transition program IDs and function names.
    fn locator_map(&self) -> Result<Self::LocatorMap>;
    /// Returns the transition inputs.
    fn input_map(&self) -> Result<Self::InputMap>;
    /// Returns the transition outputs.
    fn output_map(&self) -> Result<Self::OutputMap>;
    /// Returns the transition proofs.
    fn proof_map(&self) -> Result<Self::ProofMap>;
    /// Returns the transition public keys.
    fn tpk_map(&self) -> Result<Self::TPKMap>;
    /// Returns the transition commitments.
    fn tcm_map(&self) -> Result<Self::TCMMap>;
    /// Returns the transition fees.
    fn fee_map(&self) -> Result<Self::FeeMap>;

    /// Opens the transition store.
    fn open(&self) -> Result<TransitionStore<N, Self>>
    where
        Self: Sized,
    {
        Ok(TransitionStore::new(
            self.locator_map()?,
            self.input_map()?,
            self.output_map()?,
            self.proof_map()?,
            self.tpk_map()?,
            self.tcm_map()?,
            self.fee_map()?,
        ))
    }
}

/// An in-memory transition input storage.
#[derive(Clone)]
pub struct TransitionMemory<N: Network> {
    /// The transition program IDs and function names.
    locator_map: MemoryMap<N::TransitionID, (ProgramID<N>, Identifier<N>)>,
    /// The transition inputs.
    input_map: InputMemory<N>,
    /// The transition outputs.
    output_map: OutputMemory<N>,
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
            input_map: InputMemory::new(),
            output_map: OutputMemory::new(),
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
    type InputMap = InputMemory<N>;
    type OutputMap = OutputMemory<N>;
    type ProofMap = MemoryMap<N::TransitionID, Proof<N>>;
    type TPKMap = MemoryMap<N::TransitionID, Group<N>>;
    type TCMMap = MemoryMap<N::TransitionID, Field<N>>;
    type FeeMap = MemoryMap<N::TransitionID, i64>;

    /// Returns the transition program IDs and function names.
    fn locator_map(&self) -> Result<Self::LocatorMap> {
        Ok(self.locator_map.clone())
    }

    /// Returns the transition inputs.
    fn input_map(&self) -> Result<Self::InputMap> {
        Ok(self.input_map.clone())
    }

    /// Returns the transition outputs.
    fn output_map(&self) -> Result<Self::OutputMap> {
        Ok(self.output_map.clone())
    }

    /// Returns the transition proofs.
    fn proof_map(&self) -> Result<Self::ProofMap> {
        Ok(self.proof_map.clone())
    }

    /// Returns the transition public keys.
    fn tpk_map(&self) -> Result<Self::TPKMap> {
        Ok(self.tpk_map.clone())
    }

    /// Returns the transition commitments.
    fn tcm_map(&self) -> Result<Self::TCMMap> {
        Ok(self.tcm_map.clone())
    }

    /// Returns the transition fees.
    fn fee_map(&self) -> Result<Self::FeeMap> {
        Ok(self.fee_map.clone())
    }
}

pub struct TransitionStore<N: Network, T: TransitionStorage<N>> {
    /// The map of transition program IDs and function names.
    locator: T::LocatorMap,
    /// The map of transition inputs.
    inputs: T::InputMap,
    /// The map of transition outputs.
    outputs: T::OutputMap,
    /// The map of transition proofs.
    proof: T::ProofMap,
    /// The map of transition public keys.
    tpk: T::TPKMap,
    /// The map of transition commitments.
    tcm: T::TCMMap,
    /// The map of transition fees.
    fee: T::FeeMap,
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Initializes a new transition store from the given maps.
    pub fn new(
        locator: T::LocatorMap,
        inputs: T::InputMap,
        outputs: T::OutputMap,
        proof: T::ProofMap,
        tpk: T::TPKMap,
        tcm: T::TCMMap,
        fee: T::FeeMap,
    ) -> Self {
        Self { locator, inputs, outputs, proof, tpk, tcm, fee }
    }

    /// Initializes a new transition store from the given transition storage.
    pub fn from(storage: T) -> Result<Self> {
        storage.open()
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
