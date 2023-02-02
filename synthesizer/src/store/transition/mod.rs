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
    block::{Input, Output, Transition},
    cow_to_cloned,
    cow_to_copied,
    snark::Proof,
    store::helpers::{memory_map::MemoryMap, Map, MapRead},
};
use console::{
    network::prelude::*,
    program::{Ciphertext, Identifier, Plaintext, ProgramID, Record, Value},
    types::{Field, Group},
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transition storage.
pub trait TransitionStorage<N: Network>: Clone + Send + Sync {
    /// The transition program IDs and function names.
    type LocatorMap: for<'a> Map<'a, N::TransitionID, (ProgramID<N>, Identifier<N>)>;
    /// The transition inputs.
    type InputStorage: InputStorage<N>;
    /// The transition outputs.
    type OutputStorage: OutputStorage<N>;
    /// The transition finalize inputs.
    type FinalizeMap: for<'a> Map<'a, N::TransitionID, Option<Vec<Value<N>>>>;
    /// The transition proofs.
    type ProofMap: for<'a> Map<'a, N::TransitionID, Proof<N>>;
    /// The transition public keys.
    type TPKMap: for<'a> Map<'a, N::TransitionID, Group<N>>;
    /// The mapping of `transition public key` to `transition ID`.
    type ReverseTPKMap: for<'a> Map<'a, Group<N>, N::TransitionID>;
    /// The transition commitments.
    type TCMMap: for<'a> Map<'a, N::TransitionID, Field<N>>;
    /// The mapping of `transition commitment` to `transition ID`.
    type ReverseTCMMap: for<'a> Map<'a, Field<N>, N::TransitionID>;
    /// The transition fees.
    type FeeMap: for<'a> Map<'a, N::TransitionID, i64>;

    /// Initializes the transition storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Returns the transition program IDs and function names.
    fn locator_map(&self) -> &Self::LocatorMap;
    /// Returns the transition input store.
    fn input_store(&self) -> &InputStore<N, Self::InputStorage>;
    /// Returns the transition output store.
    fn output_store(&self) -> &OutputStore<N, Self::OutputStorage>;
    /// Returns the transition finalize inputs map.
    fn finalize_map(&self) -> &Self::FinalizeMap;
    /// Returns the transition proofs map.
    fn proof_map(&self) -> &Self::ProofMap;
    /// Returns the transition public keys map.
    fn tpk_map(&self) -> &Self::TPKMap;
    /// Returns the reverse `tpk` map.
    fn reverse_tpk_map(&self) -> &Self::ReverseTPKMap;
    /// Returns the transition commitments map.
    fn tcm_map(&self) -> &Self::TCMMap;
    /// Returns the reverse `tcm` map.
    fn reverse_tcm_map(&self) -> &Self::ReverseTCMMap;
    /// Returns the transition fees.
    fn fee_map(&self) -> &Self::FeeMap;

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        debug_assert!(self.input_store().dev() == self.output_store().dev());
        self.input_store().dev()
    }

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.locator_map().start_atomic();
        self.input_store().start_atomic();
        self.output_store().start_atomic();
        self.finalize_map().start_atomic();
        self.proof_map().start_atomic();
        self.tpk_map().start_atomic();
        self.reverse_tpk_map().start_atomic();
        self.tcm_map().start_atomic();
        self.reverse_tcm_map().start_atomic();
        self.fee_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.locator_map().is_atomic_in_progress()
            || self.input_store().is_atomic_in_progress()
            || self.output_store().is_atomic_in_progress()
            || self.finalize_map().is_atomic_in_progress()
            || self.proof_map().is_atomic_in_progress()
            || self.tpk_map().is_atomic_in_progress()
            || self.reverse_tpk_map().is_atomic_in_progress()
            || self.tcm_map().is_atomic_in_progress()
            || self.reverse_tcm_map().is_atomic_in_progress()
            || self.fee_map().is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.locator_map().abort_atomic();
        self.input_store().abort_atomic();
        self.output_store().abort_atomic();
        self.finalize_map().abort_atomic();
        self.proof_map().abort_atomic();
        self.tpk_map().abort_atomic();
        self.reverse_tpk_map().abort_atomic();
        self.tcm_map().abort_atomic();
        self.reverse_tcm_map().abort_atomic();
        self.fee_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.locator_map().finish_atomic()?;
        self.input_store().finish_atomic()?;
        self.output_store().finish_atomic()?;
        self.finalize_map().finish_atomic()?;
        self.proof_map().finish_atomic()?;
        self.tpk_map().finish_atomic()?;
        self.reverse_tpk_map().finish_atomic()?;
        self.tcm_map().finish_atomic()?;
        self.reverse_tcm_map().finish_atomic()?;
        self.fee_map().finish_atomic()
    }

    /// Stores the given `transition` into storage.
    fn insert(&self, transition: &Transition<N>) -> Result<()> {
        // Check if an atomic batch write is already in progress.
        let is_part_of_atomic_batch = self.is_atomic_in_progress();

        // Start an atomic batch write operation IFF it's not already part of one.
        if !is_part_of_atomic_batch {
            self.start_atomic();
        }

        let run_atomic_ops = || -> Result<()> {
            // Retrieve the transition ID.
            let transition_id = *transition.id();
            // Store the program ID and function name.
            self.locator_map().insert(transition_id, (*transition.program_id(), *transition.function_name()))?;
            // Store the inputs.
            self.input_store().insert(transition_id, transition.inputs())?;
            // Store the outputs.
            self.output_store().insert(transition_id, transition.outputs())?;
            // Store the finalize inputs.
            self.finalize_map().insert(transition_id, transition.finalize().cloned())?;
            // Store the proof.
            self.proof_map().insert(transition_id, transition.proof().clone())?;
            // Store `tpk`.
            self.tpk_map().insert(transition_id, *transition.tpk())?;
            // Store the reverse `tpk` entry.
            self.reverse_tpk_map().insert(*transition.tpk(), transition_id)?;
            // Store `tcm`.
            self.tcm_map().insert(transition_id, *transition.tcm())?;
            // Store the reverse `tcm` entry.
            self.reverse_tcm_map().insert(*transition.tcm(), transition_id)?;
            // Store the fee.
            self.fee_map().insert(transition_id, *transition.fee())?;

            Ok(())
        };

        // Abort if any of the underlying operations has failed.
        run_atomic_ops().map_err(|err| {
            self.abort_atomic();
            err
        })?;

        // Finish an atomic batch write operation IFF it's not already part of one.
        if !is_part_of_atomic_batch {
            self.finish_atomic()?;
        }

        Ok(())
    }

    /// Removes the input for the given `transition ID`.
    fn remove(&self, transition_id: &N::TransitionID) -> Result<()> {
        // Retrieve the `tpk`.
        let tpk = match self.tpk_map().get(transition_id)? {
            Some(tpk) => cow_to_copied!(tpk),
            None => return Ok(()),
        };
        // Retrieve the `tcm`.
        let tcm = match self.tcm_map().get(transition_id)? {
            Some(tcm) => cow_to_copied!(tcm),
            None => return Ok(()),
        };

        // Check if an atomic batch write is already in progress.
        let is_part_of_atomic_batch = self.is_atomic_in_progress();

        // Start an atomic batch write operation IFF it's not already part of one.
        if !is_part_of_atomic_batch {
            self.start_atomic();
        }

        let run_atomic_ops = || -> Result<()> {
            // Remove the program ID and function name.
            self.locator_map().remove(transition_id)?;
            // Remove the inputs.
            self.input_store().remove(transition_id)?;
            // Remove the outputs.
            self.output_store().remove(transition_id)?;
            // Remove the finalize inputs.
            self.finalize_map().remove(transition_id)?;
            // Remove the proof.
            self.proof_map().remove(transition_id)?;
            // Remove `tpk`.
            self.tpk_map().remove(transition_id)?;
            // Remove the reverse `tpk` entry.
            self.reverse_tpk_map().remove(&tpk)?;
            // Remove `tcm`.
            self.tcm_map().remove(transition_id)?;
            // Remove the reverse `tcm` entry.
            self.reverse_tcm_map().remove(&tcm)?;
            // Remove the fee.
            self.fee_map().remove(transition_id)?;

            Ok(())
        };

        // Abort if any of the underlying operations has failed.
        run_atomic_ops().map_err(|err| {
            self.abort_atomic();
            err
        })?;

        // Finish an atomic batch write operation IFF it's not already part of one.
        if !is_part_of_atomic_batch {
            self.finish_atomic()?;
        }

        Ok(())
    }

    /// Returns the transition for the given `transition ID`.
    fn get(&self, transition_id: &N::TransitionID) -> Result<Option<Transition<N>>> {
        // Retrieve the program ID and function name.
        let (program_id, function_name) = match self.locator_map().get(transition_id)? {
            Some(locator) => cow_to_cloned!(locator),
            None => return Ok(None),
        };
        // Retrieve the inputs.
        let inputs = self.input_store().get_inputs(transition_id)?;
        // Retrieve the outputs.
        let outputs = self.output_store().get_outputs(transition_id)?;
        // Retrieve the finalize inputs.
        let finalize = self.finalize_map().get(transition_id)?;
        // Retrieve the proof.
        let proof = self.proof_map().get(transition_id)?;
        // Retrieve `tpk`.
        let tpk = self.tpk_map().get(transition_id)?;
        // Retrieve `tcm`.
        let tcm = self.tcm_map().get(transition_id)?;
        // Retrieve the fee.
        let fee = self.fee_map().get(transition_id)?;

        match (finalize, proof, tpk, tcm, fee) {
            (Some(finalize), Some(proof), Some(tpk), Some(tcm), Some(fee)) => {
                // Construct the transition.
                let transition = Transition::new(
                    program_id,
                    function_name,
                    inputs,
                    outputs,
                    cow_to_cloned!(finalize),
                    cow_to_cloned!(proof),
                    cow_to_cloned!(tpk),
                    cow_to_cloned!(tcm),
                    cow_to_cloned!(fee),
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
}

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
    /// The transition proofs.
    proof_map: MemoryMap<N::TransitionID, Proof<N>>,
    /// The transition public keys.
    tpk_map: MemoryMap<N::TransitionID, Group<N>>,
    /// The reverse `tpk` map.
    reverse_tpk_map: MemoryMap<Group<N>, N::TransitionID>,
    /// The transition commitments.
    tcm_map: MemoryMap<N::TransitionID, Field<N>>,
    /// The reverse `tcm` map.
    reverse_tcm_map: MemoryMap<Field<N>, N::TransitionID>,
    /// The transition fees.
    fee_map: MemoryMap<N::TransitionID, i64>,
}

#[rustfmt::skip]
impl<N: Network> TransitionStorage<N> for TransitionMemory<N> {
    type LocatorMap = MemoryMap<N::TransitionID, (ProgramID<N>, Identifier<N>)>;
    type InputStorage = InputMemory<N>;
    type OutputStorage = OutputMemory<N>;
    type FinalizeMap = MemoryMap<N::TransitionID, Option<Vec<Value<N>>>>;
    type ProofMap = MemoryMap<N::TransitionID, Proof<N>>;
    type TPKMap = MemoryMap<N::TransitionID, Group<N>>;
    type ReverseTPKMap = MemoryMap<Group<N>, N::TransitionID>;
    type TCMMap = MemoryMap<N::TransitionID, Field<N>>;
    type ReverseTCMMap = MemoryMap<Field<N>, N::TransitionID>;
    type FeeMap = MemoryMap<N::TransitionID, i64>;

    /// Initializes the transition storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            locator_map: MemoryMap::default(),
            input_store: InputStore::open(dev)?,
            output_store: OutputStore::open(dev)?,
            finalize_map: MemoryMap::default(),
            proof_map: MemoryMap::default(),
            tpk_map: MemoryMap::default(),
            reverse_tpk_map: MemoryMap::default(),
            tcm_map: MemoryMap::default(),
            reverse_tcm_map: MemoryMap::default(),
            fee_map: MemoryMap::default(),
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

    /// Returns the transition proofs.
    fn proof_map(&self) -> &Self::ProofMap {
        &self.proof_map
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
    /// The map of transition finalize inputs.
    finalize: T::FinalizeMap,
    /// The map of transition proofs.
    proof: T::ProofMap,
    /// The map of transition public keys.
    tpk: T::TPKMap,
    /// The reverse `tpk` map.
    reverse_tpk: T::ReverseTPKMap,
    /// The map of transition commitments.
    tcm: T::TCMMap,
    /// The reverse `tcm` map.
    reverse_tcm: T::ReverseTCMMap,
    /// The map of transition fees.
    fee: T::FeeMap,
    /// The transition storage.
    storage: T,
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Initializes the transition store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the transition storage.
        let storage = T::open(dev)?;
        // Return the transition store.
        Ok(Self {
            locator: storage.locator_map().clone(),
            inputs: (*storage.input_store()).clone(),
            outputs: (*storage.output_store()).clone(),
            finalize: storage.finalize_map().clone(),
            proof: storage.proof_map().clone(),
            tpk: storage.tpk_map().clone(),
            reverse_tpk: storage.reverse_tpk_map().clone(),
            tcm: storage.tcm_map().clone(),
            reverse_tcm: storage.reverse_tcm_map().clone(),
            fee: storage.fee_map().clone(),
            storage,
        })
    }

    /// Initializes a transition store from storage.
    pub fn from(storage: T) -> Self {
        Self {
            locator: storage.locator_map().clone(),
            inputs: (*storage.input_store()).clone(),
            outputs: (*storage.output_store()).clone(),
            finalize: storage.finalize_map().clone(),
            proof: storage.proof_map().clone(),
            tpk: storage.tpk_map().clone(),
            reverse_tpk: storage.reverse_tpk_map().clone(),
            tcm: storage.tcm_map().clone(),
            reverse_tcm: storage.reverse_tcm_map().clone(),
            fee: storage.fee_map().clone(),
            storage,
        }
    }

    /// Stores the given `transition` into storage.
    pub fn insert(&self, transition: &Transition<N>) -> Result<()> {
        self.storage.insert(transition)
    }

    /// Removes the input for the given `transition ID`.
    pub fn remove(&self, transition_id: &N::TransitionID) -> Result<()> {
        self.storage.remove(transition_id)
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

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns the transition ID that contains the given `input ID` or `output ID`.
    pub fn find_transition_id(&self, id: &Field<N>) -> Result<N::TransitionID> {
        // Start by checking the output IDs (which is the more likely case).
        if let Some(transition_id) = self.outputs.find_transition_id(id)? {
            return Ok(transition_id);
        }
        // Then check the input IDs.
        if let Some(transition_id) = self.inputs.find_transition_id(id)? {
            return Ok(transition_id);
        }
        // Throw an error.
        bail!("Failed to find the transition ID for the given input or output ID '{id}'")
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns the transition for the given `transition ID`.
    pub fn get_transition(&self, transition_id: &N::TransitionID) -> Result<Option<Transition<N>>> {
        self.storage.get(transition_id)
    }

    /// Returns the program ID for the given `transition ID`.
    pub fn get_program_id(&self, transition_id: &N::TransitionID) -> Result<Option<ProgramID<N>>> {
        Ok(self.locator.get(transition_id)?.map(|locator| match locator {
            Cow::Borrowed((program_id, _)) => *program_id,
            Cow::Owned((program_id, _)) => program_id,
        }))
    }

    /// Returns the function name for the given `transition ID`.
    pub fn get_function_name(&self, transition_id: &N::TransitionID) -> Result<Option<Identifier<N>>> {
        Ok(self.locator.get(transition_id)?.map(|locator| match locator {
            Cow::Borrowed((_, function_name)) => *function_name,
            Cow::Owned((_, function_name)) => function_name,
        }))
    }

    /// Returns the input IDs for the given `transition ID`.
    pub fn get_input_ids(&self, transition_id: &N::TransitionID) -> Result<Vec<Field<N>>> {
        self.inputs.get_input_ids(transition_id)
    }

    /// Returns the inputs for the given `transition ID`.
    pub fn get_inputs(&self, transition_id: &N::TransitionID) -> Result<Vec<Input<N>>> {
        self.inputs.get_inputs(transition_id)
    }

    /// Returns the output IDs for the given `transition ID`.
    pub fn get_output_ids(&self, transition_id: &N::TransitionID) -> Result<Vec<Field<N>>> {
        self.outputs.get_output_ids(transition_id)
    }

    /// Returns the outputs for the given `transition ID`.
    pub fn get_outputs(&self, transition_id: &N::TransitionID) -> Result<Vec<Output<N>>> {
        self.outputs.get_outputs(transition_id)
    }

    /// Returns the finalize inputs for the given `transition ID`.
    pub fn get_finalize(&self, transition_id: &N::TransitionID) -> Result<Option<Vec<Value<N>>>> {
        match self.finalize.get(transition_id)? {
            Some(finalize) => Ok(cow_to_cloned!(finalize)),
            None => bail!("Missing transition '{transition_id}' - cannot get finalize inputs"),
        }
    }

    /// Returns the record for the given `commitment`.
    ///
    /// If the record exists, `Ok(Some(record))` is returned.
    /// If the record was purged, `Ok(None)` is returned.
    /// If the record does not exist, `Err(error)` is returned.
    pub fn get_record(&self, commitment: &Field<N>) -> Result<Option<Record<N, Ciphertext<N>>>> {
        self.outputs.get_record(commitment)
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns `true` if the given transition ID exists.
    pub fn contains_transition_id(&self, transition_id: &N::TransitionID) -> Result<bool> {
        self.locator.contains_key(transition_id)
    }

    /* Input */

    /// Returns `true` if the given input ID exists.
    pub fn contains_input_id(&self, input_id: &Field<N>) -> Result<bool> {
        self.inputs.contains_input_id(input_id)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> Result<bool> {
        self.inputs.contains_serial_number(serial_number)
    }

    /// Returns `true` if the given tag exists.
    pub fn contains_tag(&self, tag: &Field<N>) -> Result<bool> {
        self.inputs.contains_tag(tag)
    }

    /* Output */

    /// Returns `true` if the given output ID exists.
    pub fn contains_output_id(&self, output_id: &Field<N>) -> Result<bool> {
        self.outputs.contains_output_id(output_id)
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> Result<bool> {
        self.outputs.contains_commitment(commitment)
    }

    /// Returns `true` if the given checksum exists.
    pub fn contains_checksum(&self, checksum: &Field<N>) -> bool {
        self.outputs.contains_checksum(checksum)
    }

    /// Returns `true` if the given nonce exists.
    pub fn contains_nonce(&self, nonce: &Group<N>) -> Result<bool> {
        self.outputs.contains_nonce(nonce)
    }

    /* Metadata */

    /// Returns `true` if the given transition public key exists.
    pub fn contains_tpk(&self, tpk: &Group<N>) -> Result<bool> {
        self.reverse_tpk.contains_key(tpk)
    }

    /// Returns `true` if the given transition commitment exists.
    pub fn contains_tcm(&self, tcm: &Field<N>) -> Result<bool> {
        self.reverse_tcm.contains_key(tcm)
    }
}

impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransitionID>> {
        self.fee.keys()
    }

    /* Input */

    /// Returns an iterator over the input IDs, for all transition inputs.
    pub fn input_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.inputs.input_ids()
    }

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

    /// Returns an iterator over the output IDs, for all transition outputs.
    pub fn output_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.outputs.output_ids()
    }

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
    /* Input */

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

    /// Returns an iterator over the `(commitment, record)` pairs, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = (Cow<'_, Field<N>>, Cow<'_, Record<N, Ciphertext<N>>>)> {
        self.outputs.records()
    }

    /* Metadata */

    /// Returns an iterator over the proofs, for all transitions.
    pub fn proofs(&self) -> impl '_ + Iterator<Item = Cow<'_, Proof<N>>> {
        self.proof.values()
    }

    /// Returns an iterator over the transition public keys, for all transitions.
    pub fn tpks(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.tpk.values()
    }

    /// Returns an iterator over the transition commitments, for all transitions.
    pub fn tcms(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.tcm.values()
    }

    /// Returns an iterator over the transition fees, for all transitions.
    pub fn fees(&self) -> impl '_ + Iterator<Item = Cow<'_, i64>> {
        self.fee.values()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        let rng = &mut TestRng::default();

        // Sample the transitions.
        let transaction = crate::vm::test_helpers::sample_execution_transaction(rng);
        let transitions = transaction
            .transitions()
            .chain([crate::process::test_helpers::sample_transition()].iter())
            .cloned()
            .collect::<Vec<_>>();

        // Ensure there is at least 2 transition.
        println!("\n\nNumber of transitions: {}\n", transitions.len());
        assert!(transitions.len() > 1, "\n\nNumber of transitions: {}\n", transitions.len());

        // Initialize a new transition store.
        let transition_store = TransitionMemory::open(None).unwrap();

        // Test each transition in isolation.
        for transition in transitions.iter() {
            // Retrieve the transition ID.
            let transition_id = *transition.id();

            // Ensure the transition does not exist.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);

            // Insert the transition.
            transition_store.insert(transition).unwrap();

            // Retrieve the transition.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(Some(transition.clone()), candidate);

            // Remove the transition.
            transition_store.remove(&transition_id).unwrap();

            // Retrieve the transition.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);
        }

        // Insert every transition.
        for transition in transitions.iter() {
            // Retrieve the transition ID.
            let transition_id = *transition.id();

            // Ensure the transition does not exist.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);

            // Insert the transition.
            transition_store.insert(transition).unwrap();

            // Ensure the transition exists.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(Some(transition.clone()), candidate);
        }

        // Get every transition (in reverse).
        for transition in transitions.iter().rev() {
            // Retrieve the transition ID.
            let transition_id = *transition.id();

            // Retrieve the transition.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(Some(transition.clone()), candidate);
        }

        // Remove every transition (in reverse).
        for transition in transitions.iter().rev() {
            // Retrieve the transition ID.
            let transition_id = *transition.id();

            // Remove the transition.
            transition_store.remove(&transition_id).unwrap();

            // Ensure the transition does not exist.
            let candidate = transition_store.get(&transition_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
