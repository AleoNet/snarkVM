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

use crate::{Parameters, ProgramCircuit};
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree, MerkleTreeDigest},
    prelude::*,
};

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A circuit tree defines all possible state transitions for a record.
#[derive(Derivative)]
#[derivative(Debug(bound = "C: Parameters"))]
pub struct CircuitTree<C: Parameters> {
    #[derivative(Debug = "ignore")]
    tree: MerkleTree<C::ProgramIDTreeParameters>,
    #[derivative(Debug = "ignore")]
    circuits: HashMap<u8, Box<dyn ProgramCircuit<C>>>,
    last_circuit_index: u8,
}

impl<C: Parameters> CircuitTree<C> {
    /// Initializes an empty circuit tree.
    pub fn new() -> Result<Self> {
        Ok(Self {
            tree: MerkleTree::<C::ProgramIDTreeParameters>::new::<<C::ProgramSNARK as SNARK>::VerifyingKey>(
                Arc::new(C::program_id_tree_parameters().clone()),
                &vec![],
            )?,
            circuits: Default::default(),
            last_circuit_index: 0,
        })
    }

    /// Adds the given circuit to the tree, returning its circuit index in the tree.
    pub fn add(&mut self, circuit: &Box<dyn ProgramCircuit<C>>) -> Result<u8> {
        self.tree = self
            .tree
            .rebuild(self.last_circuit_index as usize, &[circuit.verifying_key()])?;

        self.circuits.insert(self.last_circuit_index, *circuit.clone());
        self.last_circuit_index += 1;
        Ok(self.last_circuit_index - 1)
    }

    /// Adds all given circuits to the tree, returning the start and ending circuit index in the tree.
    pub fn add_all(&mut self, circuits: &[Box<dyn ProgramCircuit<C>>]) -> Result<(u8, u8)> {
        // Ensure the list of circuits is non-empty.
        if circuits.is_empty() {
            return Err(anyhow!("The list of of circuits must be non-empty"));
        }

        let circuit_verifying_keys: Vec<_> = circuits.iter().map(|c| c.verifying_key()).collect();
        self.tree = self
            .tree
            .rebuild(self.last_circuit_index as usize, &circuit_verifying_keys)?;

        let start_index = self.last_circuit_index;
        for circuit in circuits {
            self.circuits.insert(self.last_circuit_index, *circuit.clone());
            self.last_circuit_index += 1;
        }
        let end_index = self.last_circuit_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns the circuit given the circuit index, if it exists.
    pub fn get_circuit(&self, circuit_index: u8) -> Option<&Box<dyn ProgramCircuit<C>>> {
        self.circuits.get(&circuit_index)
    }

    /// Returns the circuit ID given the circuit index, if it exists.
    pub fn get_circuit_id(&self, circuit_index: u8) -> Option<&Vec<u8>> {
        self.circuits.get(&circuit_index).and_then(|c| Some(c.circuit_id()))
    }

    /// Returns the program proof (the Merkle path for a given circuit index).
    pub fn get_program_proof(&self, circuit_index: u8) -> Result<MerklePath<C::ProgramIDTreeParameters>> {
        match self.get_circuit(circuit_index) {
            Some(circuit) => Ok(self
                .tree
                .generate_proof(circuit_index as usize, circuit.verifying_key())?),
            _ => Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        }
    }

    /// Returns the program ID.
    pub fn to_program_id(&self) -> &MerkleTreeDigest<C::ProgramIDTreeParameters> {
        &self.tree.root()
    }
}

impl<C: Parameters> Default for CircuitTree<C> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
