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

use crate::{Executable, Network, ProgramCircuit, ProgramError, ProgramExecutable, ProgramScheme};
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    prelude::*,
};
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A program defines all possible state transitions for a record.
#[derive(Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub struct Program<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: MerkleTree<N::ProgramCircuitsTreeParameters>,
    #[derivative(Debug = "ignore")]
    circuits: HashMap<N::ProgramCircuitID, (u8, ProgramCircuit<N>)>,
    last_circuit_index: u8,
}

impl<N: Network> ProgramScheme<N> for Program<N> {
    /// Initializes an instance of the program with the given circuits.
    fn new(circuits: Vec<ProgramCircuit<N>>) -> Result<Self, ProgramError> {
        // Initialize a new circuits tree, and add all circuits to the tree.
        let mut program = Self {
            tree: MerkleTree::<N::ProgramCircuitsTreeParameters>::new::<N::ProgramCircuitID>(
                Arc::new(N::program_circuits_tree_parameters().clone()),
                &vec![],
            )?,
            circuits: Default::default(),
            last_circuit_index: 0,
        };
        program.add_all(circuits)?;

        Ok(program)
    }

    /// Initializes an instance of the noop program.
    fn new_noop() -> Result<Self, ProgramError> {
        // Initialize a new circuits tree, and add all circuits to the tree.
        let mut program = Self {
            tree: MerkleTree::<N::ProgramCircuitsTreeParameters>::new::<N::ProgramCircuitID>(
                Arc::new(N::program_circuits_tree_parameters().clone()),
                &vec![],
            )?,
            circuits: Default::default(),
            last_circuit_index: 0,
        };
        program.add(ProgramCircuit::Noop)?;

        Ok(program)
    }

    /// Returns the program ID.
    fn program_id(&self) -> N::ProgramID {
        *self.tree.root()
    }

    /// Returns `true` if the given circuit ID exists in the program.
    fn contains_circuit(&self, circuit_id: &N::ProgramCircuitID) -> bool {
        self.circuits.get(circuit_id).is_some()
    }

    /// Returns the circuit given the circuit ID, if it exists.
    fn to_circuit(&self, circuit_id: &N::ProgramCircuitID) -> Option<&ProgramCircuit<N>> {
        self.circuits.get(circuit_id).and_then(|(__, circuit)| Some(circuit))
    }

    /// Returns the program path (the Merkle path for a given circuit ID).
    fn to_program_path(
        &self,
        circuit_id: &N::ProgramCircuitID,
    ) -> Result<MerklePath<N::ProgramCircuitsTreeParameters>, ProgramError> {
        match self.get_circuit_index(circuit_id) {
            Some(index) => Ok(self.tree.generate_proof(index as usize, circuit_id)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", circuit_id)).into()),
        }
    }

    /// Returns an instance of an executable given the circuit ID, if it exists.
    fn to_executable(&self, circuit_id: &N::ProgramCircuitID) -> Result<Executable<N>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.to_circuit(circuit_id) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeaf(format!("{}", circuit_id)).into()),
        };
        debug_assert_eq!(circuit.circuit_id(), *circuit_id);

        let program_path = self.to_program_path(circuit_id)?;
        debug_assert!(program_path.verify(&self.program_id(), circuit_id)?);

        Ok(Executable::new(self.program_id(), circuit.clone(), program_path)?)
    }
}

impl<N: Network> Program<N> {
    /// TODO (howardwu): Add safety checks for u8 (max 255 circuits).
    /// Adds the given circuit to the tree, returning its circuit index in the tree.
    fn add(&mut self, circuit: ProgramCircuit<N>) -> Result<u8> {
        // Ensure the circuit does not already exist in the tree.
        if self.contains_circuit(&circuit.circuit_id()) {
            return Err(MerkleError::Message(format!("Duplicate circuit {}", circuit.circuit_id())).into());
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
    fn add_all(&mut self, circuits: Vec<ProgramCircuit<N>>) -> Result<(u8, u8)> {
        // Ensure the list of given circuits is non-empty.
        if circuits.is_empty() {
            return Err(anyhow!("The list of given circuits must be non-empty"));
        }

        // Construct a list of circuit IDs.
        let circuit_ids: Vec<_> = circuits.iter().map(|c| c.circuit_id()).collect();

        // Ensure the list of given circuit IDs is unique.
        if has_duplicates(circuit_ids.iter()) {
            return Err(anyhow!("The list of given circuits contains duplicates"));
        }

        // Ensure the circuits do not already exist in the tree.
        let duplicate_circuits: Vec<_> = circuit_ids.iter().filter(|id| self.contains_circuit(id)).collect();
        if !duplicate_circuits.is_empty() {
            return Err(anyhow!("The list of given circuits contains already existing circuits"));
        }

        self.tree = self.tree.rebuild(self.last_circuit_index as usize, &circuit_ids)?;

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

    /// Returns the circuit given the circuit index, if it exists.
    fn find_circuit_by_index(&self, circuit_index: u8) -> Option<&ProgramCircuit<N>> {
        self.circuits
            .iter()
            .find_map(|(_, (index, circuit))| match *index == circuit_index {
                true => Some(circuit),
                false => None,
            })
    }

    /// Returns the circuit index given the circuit ID, if it exists.
    fn get_circuit_index(&self, circuit_id: &N::ProgramCircuitID) -> Option<u8> {
        self.circuits.get(circuit_id).and_then(|(index, _)| Some(*index))
    }
}
