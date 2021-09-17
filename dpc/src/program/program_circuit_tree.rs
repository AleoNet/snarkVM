// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{Network, ProgramCircuit};
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree, MerkleTreeDigest},
    prelude::*,
};

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A program circuit tree defines all possible state transitions for a record.
#[derive(Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub struct ProgramCircuitTree<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: MerkleTree<N::ProgramCircuitTreeParameters>,
    #[derivative(Debug = "ignore")]
    circuits: HashMap<N::ProgramCircuitID, (u8, Box<dyn ProgramCircuit<N>>)>,
    last_circuit_index: u8,
}

impl<N: Network> ProgramCircuitTree<N> {
    /// Initializes an empty circuit tree.
    pub fn new() -> Result<Self> {
        Ok(Self {
            tree: MerkleTree::<N::ProgramCircuitTreeParameters>::new::<N::ProgramCircuitID>(
                Arc::new(N::program_circuit_tree_parameters().clone()),
                &vec![],
            )?,
            circuits: Default::default(),
            last_circuit_index: 0,
        })
    }

    /// TODO (howardwu): Add safety checks for u8 (max 255 circuits).
    /// Adds the given circuit to the tree, returning its circuit index in the tree.
    pub fn add(&mut self, circuit: Box<dyn ProgramCircuit<N>>) -> Result<u8> {
        // Ensure the circuit does not already exist in the tree.
        if self.contains_circuit(circuit.circuit_id()) {
            return Err(MerkleError::MissingLeaf(format!("{}", circuit.circuit_id())).into());
        }

        self.tree = self
            .tree
            .rebuild(self.last_circuit_index as usize, &[circuit.circuit_id()])?;

        self.circuits
            .insert(circuit.circuit_id().clone(), (self.last_circuit_index, circuit));

        self.last_circuit_index += 1;
        Ok(self.last_circuit_index - 1)
    }

    /// TODO (howardwu): Add safety checks for u8 (max 255 circuits).
    /// Adds all given circuits to the tree, returning the start and ending circuit index in the tree.
    pub fn add_all(&mut self, circuits: Vec<Box<dyn ProgramCircuit<N>>>) -> Result<(u8, u8)> {
        // Ensure the list of circuits is non-empty.
        if circuits.is_empty() {
            return Err(anyhow!("The list of of circuits must be non-empty"));
        }

        // Ensure the circuits do not already exist in the tree.
        let circuits: Vec<_> = circuits
            .into_iter()
            .filter(|c| !self.contains_circuit(c.circuit_id()))
            .collect();

        self.tree = self.tree.rebuild(
            self.last_circuit_index as usize,
            &circuits.iter().map(|c| c.circuit_id()).collect::<Vec<_>>(),
        )?;

        let start_index = self.last_circuit_index;
        let num_circuits = circuits.len();

        self.circuits.extend(
            circuits
                .into_iter()
                .enumerate()
                .map(|(index, circuit)| (circuit.circuit_id().clone(), (start_index + index as u8, circuit))),
        );

        self.last_circuit_index += num_circuits as u8;
        let end_index = self.last_circuit_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given circuit ID exists.
    pub fn contains_circuit(&self, circuit_id: &N::ProgramCircuitID) -> bool {
        self.circuits.get(circuit_id).is_some()
    }

    /// Returns the circuit index given the circuit ID, if it exists.
    pub fn get_circuit_index(&self, circuit_id: &N::ProgramCircuitID) -> Option<u8> {
        self.circuits.get(circuit_id).and_then(|(index, _)| Some(*index))
    }

    /// Returns the circuit given the circuit ID, if it exists.
    pub fn get_circuit(&self, circuit_id: &N::ProgramCircuitID) -> Option<&Box<dyn ProgramCircuit<N>>> {
        self.circuits.get(circuit_id).and_then(|(__, circuit)| Some(circuit))
    }

    /// Returns the circuit given the circuit index, if it exists.
    pub fn find_circuit_by_index(&self, circuit_index: u8) -> Option<&Box<dyn ProgramCircuit<N>>> {
        self.circuits
            .iter()
            .find_map(|(_, (index, circuit))| match *index == circuit_index {
                true => Some(circuit),
                false => None,
            })
    }

    /// Returns the program path (the Merkle path for a given circuit ID).
    pub fn get_program_path(
        &self,
        circuit_id: &N::ProgramCircuitID,
    ) -> Result<MerklePath<N::ProgramCircuitTreeParameters>> {
        match self.get_circuit_index(circuit_id) {
            Some(index) => Ok(self.tree.generate_proof(index as usize, circuit_id)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", circuit_id)).into()),
        }
    }

    /// Returns the program ID.
    pub fn to_program_id(&self) -> &MerkleTreeDigest<N::ProgramCircuitTreeParameters> {
        self.tree.root()
    }
}

impl<N: Network> Default for ProgramCircuitTree<N> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
