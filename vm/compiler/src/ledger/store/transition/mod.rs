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
        Origin,
        Transition,
    },
    snark::Proof,
    unwrap_cow,
};
use console::{
    network::prelude::*,
    program::{Ciphertext, Identifier, Plaintext, ProgramID, Record},
    types::{Field, Group},
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition input storage.
pub trait TransitionStorage<N: Network>: Clone {
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

    /// Returns the transition for the given `transition ID`.
    fn get(&self, transition_id: &N::TransitionID) -> Result<Option<Transition<N>>> {
        // Retrieve the program ID and function name.
        let (program_id, function_name) = match self.locator_map().get(transition_id)? {
            Some(locator) => unwrap_cow!(locator),
            None => return Ok(None),
        };
        // Retrieve the inputs.
        let inputs = self.input_store().get(transition_id)?;
        // Retrieve the outputs.
        let outputs = self.output_store().get(transition_id)?;
        // Retrieve the proof.
        let proof = self.proof_map().get(transition_id)?;
        // Retrieve `tpk`.
        let tpk = self.tpk_map().get(transition_id)?;
        // Retrieve `tcm`.
        let tcm = self.tcm_map().get(transition_id)?;
        // Retrieve the fee.
        let fee = self.fee_map().get(transition_id)?;

        match (proof, tpk, tcm, fee) {
            (Some(proof), Some(tpk), Some(tcm), Some(fee)) => {
                // Construct the transition.
                let transition = Transition::new(
                    program_id,
                    function_name,
                    inputs,
                    outputs,
                    unwrap_cow!(proof),
                    unwrap_cow!(tpk),
                    unwrap_cow!(tcm),
                    unwrap_cow!(fee),
                )?;
                // Ensure the transition ID matches.
                match transition.id() == transition_id {
                    true => Ok(Some(transition)),
                    false => bail!("Mismatch in the transition ID '{transition_id}'"),
                }
            }
            _ => bail!("Transition '{transition_id}' is missing some data (possible corruption)"),
        }
    }

    /// Stores the given `transition` into storage.
    fn insert(&self, transition: Transition<N>) -> Result<()> {
        // Retrieve the transition ID.
        let transition_id = *transition.id();
        // Store the program ID and function name.
        self.locator_map().insert(transition_id, (*transition.program_id(), *transition.function_name()))?;
        // Store the inputs.
        self.input_store().insert(transition_id, transition.inputs())?;
        // Store the outputs.
        self.output_store().insert(transition_id, transition.outputs())?;
        // Store the proof.
        self.proof_map().insert(transition_id, transition.proof().clone())?;
        // Store `tpk`.
        self.tpk_map().insert(transition_id, *transition.tpk())?;
        // Store `tcm`.
        self.tcm_map().insert(transition_id, *transition.tcm())?;
        // Store the fee.
        self.fee_map().insert(transition_id, *transition.fee())?;

        Ok(())
    }

    /// Removes the input for the given `transition ID`.
    fn remove(&self, transition_id: &N::TransitionID) -> Result<()> {
        // Remove the program ID and function name.
        self.locator_map().remove(transition_id)?;
        // Remove the inputs.
        self.input_store().remove(transition_id)?;
        // Remove the outputs.
        self.output_store().remove(transition_id)?;
        // Remove the proof.
        self.proof_map().remove(transition_id)?;
        // Remove `tpk`.
        self.tpk_map().remove(transition_id)?;
        // Remove `tcm`.
        self.tcm_map().remove(transition_id)?;
        // Remove the fee.
        self.fee_map().remove(transition_id)?;

        Ok(())
    }
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

impl<N: Network> Default for TransitionMemory<N> {
    fn default() -> Self {
        Self::new()
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
    /// Returns the transition for the given `transition ID`.
    pub fn get(&self, transition_id: &N::TransitionID) -> Result<Option<Transition<N>>> {
        self.storage.get(transition_id)
    }

    /// Stores the given `transition` into storage.
    pub fn insert(&self, transition: Transition<N>) -> Result<()> {
        self.storage.insert(transition)
    }

    /// Removes the input for the given `transition ID`.
    pub fn remove(&self, transition_id: &N::TransitionID) -> Result<()> {
        self.storage.remove(transition_id)
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns an iterator over the constant input IDs, for all transition inputs that are constant.
    pub fn constant_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.constant_input_ids()
    }

    /// Returns an iterator over the public input IDs, for all transition inputs that are public.
    pub fn public_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.public_input_ids()
    }

    /// Returns an iterator over the private input IDs, for all transition inputs that are private.
    pub fn private_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.private_input_ids()
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.serial_numbers()
    }

    /// Returns an iterator over the external record input IDs, for all transition inputs that are external records.
    pub fn external_input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.external_input_ids()
    }

    /* Output */

    /// Returns an iterator over the constant output IDs, for all transition outputs that are constant.
    pub fn constant_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.constant_output_ids()
    }

    /// Returns an iterator over the public output IDs, for all transition outputs that are public.
    pub fn public_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.public_output_ids()
    }

    /// Returns an iterator over the private output IDs, for all transition outputs that are private.
    pub fn private_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.private_output_ids()
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.commitments()
    }

    /// Returns an iterator over the external record output IDs, for all transition outputs that are external records.
    pub fn external_output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.external_output_ids()
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns an iterator over the constant inputs, for all transitions.
    pub fn constant_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.inputs.constant_inputs()
    }

    /// Returns an iterator over the constant inputs, for all transitions.
    pub fn public_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.inputs.public_inputs()
    }

    /// Returns an iterator over the private inputs, for all transitions.
    pub fn private_inputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Ciphertext<N>>> {
        self.inputs.private_inputs()
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.tags()
    }

    /// Returns an iterator over the origins, for all transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = Cow<'_, Origin<N>>> {
        self.inputs.origins()
    }

    /* Output */

    /// Returns an iterator over the constant outputs, for all transitions.
    pub fn constant_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.outputs.constant_outputs()
    }

    /// Returns an iterator over the constant outputs, for all transitions.
    pub fn public_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Plaintext<N>>> {
        self.outputs.public_outputs()
    }

    /// Returns an iterator over the private outputs, for all transitions.
    pub fn private_outputs(&self) -> impl '_ + Iterator<Item = Cow<'_, Ciphertext<N>>> {
        self.outputs.private_outputs()
    }

    /// Returns an iterator over the checksums, for all transition outputs that are records.
    pub fn checksums(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.checksums()
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.outputs.nonces()
    }

    /// Returns an iterator over the records, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = Cow<'_, Record<N, Ciphertext<N>>>> {
        self.outputs.records()
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.inputs.contains_serial_number(serial_number)
    }

    /// Returns `true` if the given tag exists.
    pub fn contains_tag(&self, tag: &Field<N>) -> bool {
        self.inputs.contains_tag(tag)
    }

    /// Returns `true` if the given origin exists.
    pub fn contains_origin(&self, origin: &Origin<N>) -> bool {
        self.inputs.contains_origin(origin)
    }

    /* Output */

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.outputs.contains_commitment(commitment)
    }

    /// Returns `true` if the given checksum exists.
    pub fn contains_checksum(&self, checksum: &Field<N>) -> bool {
        self.outputs.contains_checksum(checksum)
    }

    /// Returns `true` if the given nonce exists.
    pub fn contains_nonce(&self, nonce: &Group<N>) -> bool {
        self.outputs.contains_nonce(nonce)
    }

    /// Returns `true` if the given record exists.
    pub fn contains_record(&self, record: &Record<N, Ciphertext<N>>) -> bool {
        self.outputs.contains_record(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        // Sample a transition.
        let transaction = crate::ledger::vm::test_helpers::sample_execution_transaction();
        let transition = transaction.transitions().next().unwrap();
        let transition_id = *transition.id();

        // Initialize a new transition store.
        let transition_store = TransitionMemory::new();

        // Ensure the transition does not exist.
        let candidate = transition_store.get(&transition_id).unwrap();
        assert_eq!(None, candidate);

        // Insert the transition.
        transition_store.insert(transition.clone()).unwrap();

        // Retrieve the transition.
        let candidate = transition_store.get(&transition_id).unwrap();
        assert_eq!(Some(transition.clone()), candidate);

        // Remove the transition.
        transition_store.remove(&transition_id).unwrap();

        // Retrieve the transition.
        let candidate = transition_store.get(&transition_id).unwrap();
        assert_eq!(None, candidate);
    }
}
