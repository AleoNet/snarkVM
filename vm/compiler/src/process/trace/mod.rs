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

use console::{
    network::{prelude::*, BHPMerkleTree},
    program::{InputID, OutputID, Request, Response},
    types::{Address, Field},
};

use indexmap::IndexMap;

/// N::TRACE_DEPTH
const TRANSACTION_DEPTH: u8 = 4;
/// N::TRACE_DEPTH
const TRANSITION_DEPTH: u8 = 4;

/// The trace is a two-tier Merkle tree system that tracks the inputs and outputs for all transitions in a transaction.
/// ```ignore
///                                          transaction_root
///                                               /
///                                            ...
///                                            /
///                                    transition_root_0
///                              /                            \
///                         node_0                             node_1
///                    /           \                      /               \
///                       ...                                      ...
///              /                   \                 /                     \
///         node_0       ...       node_3            node_4        ...       node_7
///       /       \              /       \         /        \              /       \
/// \[input_0, input_1, ..., input_6, input_7, output_0, output_1, ..., output_6, output_7\]
/// ```
pub struct Trace<N: Network> {
    /// The Merkle tree of transition roots.
    transaction: BHPMerkleTree<N, TRANSACTION_DEPTH>,
    /// The root for the `i-th` transition.
    roots: IndexMap<u8, Field<N>>,
    /// The leaves for the `i-th` transition.
    leaves: IndexMap<u8, Vec<Option<Field<N>>>>,
    /// The caller of the current transition.
    caller: Address<N>,
    /// The tracker for the current transition index.
    transition_index: u8,
    /// The tracker for the current input index.
    input_index: u8,
    /// The tracker for the current output index.
    output_index: u8,
    /// The boolean indicator if the trace is finalized.
    is_finalized: bool,
}

impl<N: Network> Trace<N> {
    /// Initializes a new stack trace.
    pub fn new(request: &Request<N>, response: &Response<N>) -> Result<Self> {
        // Initialize a new trace with the caller.
        let mut trace = Self {
            transaction: N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?,
            roots: IndexMap::new(),
            leaves: IndexMap::new(),
            caller: *request.caller(),
            transition_index: 0,
            input_index: 0,
            output_index: 0,
            is_finalized: false,
        };

        // Add the inputs.
        request.input_ids().iter().try_for_each(|input_id| {
            match input_id {
                // A constant input is hashed to a field element.
                InputID::Constant(input_hash) => trace.add_input(*input_hash),
                // A public input is hashed to a field element.
                InputID::Public(input_hash) => trace.add_input(*input_hash),
                // A private input is encrypted (using `tvk`) and hashed to a field element.
                InputID::Private(input_hash) => trace.add_input(*input_hash),
                // A record input is computed (using `tvk`) to its serial number.
                InputID::Record(_, serial_number) => trace.add_input(*serial_number),
                // An external record input is committed (using `tvk`) to a field element.
                InputID::ExternalRecord(input_commitment) => trace.add_input(*input_commitment),
            }
        })?;

        response.output_ids().iter().try_for_each(|output_id| {
            match output_id {
                // A constant output is hashed to a field element.
                OutputID::Constant(output_hash) => trace.add_output(*output_hash),
                // A public output is hashed to a field element.
                OutputID::Public(output_hash) => trace.add_output(*output_hash),
                // A private output is encrypted (using `tvk`) and hashed to a field element.
                OutputID::Private(output_hash) => trace.add_output(*output_hash),
                // A record output is encrypted (using `tvk`) and hashed to a field element.
                OutputID::Record(commitment, _, _) => trace.add_output(*commitment),
                // An external record output is committed (using `tvk`) to a field element.
                OutputID::ExternalRecord(output_commitment) => trace.add_output(*output_commitment),
            }
        })?;

        Ok(trace)
    }

    /// Returns the roots.
    pub const fn roots(&self) -> &IndexMap<u8, Field<N>> {
        &self.roots
    }

    /// Returns the leaves.
    pub const fn leaves(&self) -> &IndexMap<u8, Vec<Option<Field<N>>>> {
        &self.leaves
    }

    /// Returns the current caller.
    pub const fn caller(&self) -> &Address<N> {
        &self.caller
    }

    /// Adds an input to the trace.
    pub fn add_input(&mut self, input: Field<N>) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is finalized, cannot add input");
        // Ensure the input index is within the bounds of the program.
        ensure!((self.input_index as usize) < N::MAX_INPUTS, "Trace reached the maximum inputs for a program call");
        // Ensure the input is nonzero.
        ensure!(!input.is_zero(), "Input to the trace must be nonzero");

        // Add the input to the trace.
        self.leaves.entry(self.transition_index).or_default().push(Some(input));
        // Increment the input index.
        self.input_index += 1;

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Adds an output to the trace.
    pub fn add_output(&mut self, output: Field<N>) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is finalized, cannot add output");
        // Ensure the output index is within the bounds of the program.
        ensure!((self.output_index as usize) < N::MAX_OUTPUTS, "Trace reached the maximum outputs for a program call");
        // Ensure the output is nonzero.
        ensure!(!output.is_zero(), "Output to the trace must be nonzero");

        // If this is the first call to output, fast forward the input index to the end of the inputs.
        if self.output_index == 0 {
            // Pad the leaves up to the starting index for the outputs.
            self.leaves
                .entry(self.transition_index)
                .or_default()
                .extend(vec![None; N::MAX_INPUTS - self.input_index as usize]);
            // Set the input index to the end of the inputs.
            self.input_index = N::MAX_INPUTS as u8;
        }

        // Add the output to the trace.
        self.leaves.entry(self.transition_index).or_default().push(Some(output));
        // Increment the output index.
        self.output_index += 1;

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Updates the current caller, transition view key, transition index, input index, and output index.
    pub fn next_transition(&mut self, caller: Address<N>) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is finalized, cannot call next transition");
        // Ensure the number of transition roots is correct.
        ensure!(self.roots.len() == self.transition_index as usize, "Trace has incorrect number of transition roots");
        // Ensure the transition index is within the bounds of the trace.
        ensure!((self.transition_index as usize) < N::MAX_TRANSITIONS, "Trace reached the maximum transitions");
        // Ensure the input index or output index is nonzero.
        ensure!(self.input_index > 0 || self.output_index > 0, "Trace cannot transition without inputs or outputs");

        // Pad the leaves up to the starting index of the next transition.
        self.leaves
            .entry(self.transition_index)
            .or_default()
            .extend(vec![None; N::MAX_INPUTS - self.input_index as usize]);
        self.leaves
            .entry(self.transition_index)
            .or_default()
            .extend(vec![None; N::MAX_OUTPUTS - self.output_index as usize]);

        // Compute the transition tree.
        let transition = N::merkle_tree_bhp::<TRANSITION_DEPTH>(
            &self
                .leaves
                .get(&self.transition_index)
                .unwrap_or(&vec![])
                .iter()
                .map(|leaf| leaf.unwrap_or(Field::<N>::zero()).to_bits_le())
                .collect::<Vec<_>>(),
        )?;
        // Add the transition root to the Merkle tree.
        self.transaction.append(&[transition.root().to_bits_le()])?;
        self.roots.insert(self.transition_index, *transition.root());

        // Update the caller.
        self.caller = caller;

        // Increment the transition index.
        self.transition_index += 1;
        // Reset the input and output indices.
        self.input_index = 0;
        self.output_index = 0;

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Finalizes the trace.
    pub fn finalize(&mut self) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is already finalized");
        // Ensure the number of transition roots is correct.
        ensure!(self.roots.len() == self.transition_index as usize, "Trace has incorrect number of transition roots");
        // Ensure the transition index is within the bounds of the trace.
        ensure!((self.transition_index as usize) < N::MAX_TRANSITIONS, "Trace reached the maximum transitions");

        // If the input index or output index is nonzero, finalize the current transition.
        if self.input_index > 0 || self.output_index > 0 {
            // Pad the leaves up to the starting index of the next transition.
            self.leaves
                .entry(self.transition_index)
                .or_default()
                .extend(vec![None; N::MAX_INPUTS - self.input_index as usize]);
            self.leaves.entry(self.transition_index).or_default().extend(vec![
                None;
                N::MAX_OUTPUTS
                    - self.output_index as usize
            ]);

            // Compute the transition tree.
            let transition = N::merkle_tree_bhp::<TRANSITION_DEPTH>(
                &self
                    .leaves
                    .get(&self.transition_index)
                    .unwrap_or(&vec![])
                    .iter()
                    .map(|leaf| leaf.unwrap_or(Field::<N>::zero()).to_bits_le())
                    .collect::<Vec<_>>(),
            )?;
            // Add the transition root to the Merkle tree.
            self.transaction.append(&[transition.root().to_bits_le()])?;
            self.roots.insert(self.transition_index, *transition.root());

            // Increment the transition index.
            self.transition_index += 1;
            // Reset the input and output indices.
            self.input_index = 0;
            self.output_index = 0;
        }

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()?;
        // Ensure the transaction root is correct.
        self.ensure_transaction_root()
    }

    /// Ensures the current number of leaves is correct.
    pub fn ensure_num_leaves(&self) -> Result<()> {
        // Compute the number of leaves.
        let num_leaves = self.leaves.values().fold(0, |acc, v| acc + v.len());
        // Compute the expected number of leaves.
        let expected_num_leaves = self.transition_index as usize * (N::MAX_INPUTS + N::MAX_OUTPUTS) as usize
            + (self.input_index + self.output_index) as usize;
        // Ensure the number of leaves is correct.
        ensure!(
            num_leaves == expected_num_leaves,
            "Trace has an incorrect number of leaves: expected {expected_num_leaves}, found {num_leaves}"
        );
        Ok(())
    }

    /// Ensures the transaction root is correct.
    pub fn ensure_transaction_root(&self) -> Result<()> {
        // Compute the transition roots.
        self.leaves
            .values()
            .map(|leaves| {
                // Compute the leaf nodes.
                let leaf_nodes = leaves.iter().map(|leaf| leaf.unwrap_or(Field::<N>::zero()).to_bits_le());
                // Compute the transition root.
                Ok::<_, Error>(*N::merkle_tree_bhp::<TRANSITION_DEPTH>(&leaf_nodes.collect::<Vec<_>>())?.root())
            })
            .zip_eq(self.roots.values())
            .try_for_each(|(root, expected_root)| {
                let root = root?;
                match root == *expected_root {
                    true => Ok(()),
                    false => bail!("Trace has an incorrect transition root: expected {expected_root}, found {root}"),
                }
            })?;

        // Compute the transaction root.
        let root = *N::merkle_tree_bhp::<TRANSACTION_DEPTH>(
            &self.roots.values().map(|subroot| subroot.to_bits_le()).collect::<Vec<_>>(),
        )?
        .root();

        // Ensure the transaction root is correct.
        let expected_root = self.transaction.root();
        match root == *expected_root {
            true => Ok(()),
            false => bail!("Trace has an incorrect transaction root: expected {expected_root}, found {root}"),
        }
    }
}
