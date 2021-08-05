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

use crate::{
    Execution,
    NoopCircuit,
    Parameters,
    PrivateVariables,
    Program,
    ProgramCircuit,
    ProgramCircuitTree,
    ProgramError,
    PublicVariables,
};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, prelude::*};

use rand::{CryptoRng, Rng};
use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
pub struct NoopProgram<C: Parameters> {
    circuits: Arc<ProgramCircuitTree<C>>,
}

impl<C: Parameters> Program<C> for NoopProgram<C> {
    /// Initializes a new instance of the program.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, ProgramError> {
        // Initialize a new program circuit tree, and add all circuits to the tree.
        let mut circuit_tree = ProgramCircuitTree::new()?;
        circuit_tree.add_all(vec![Box::new(NoopCircuit::setup(rng)?)])?;

        Ok(Self {
            circuits: Arc::new(circuit_tree),
        })
    }

    /// Loads an instance of the program.
    fn load() -> Result<Self, ProgramError> {
        // Initialize a new program circuit tree, and add all circuits to the tree.
        let mut circuit_tree = ProgramCircuitTree::new()?;
        circuit_tree.add(Box::new(NoopCircuit::load()?))?;

        Ok(Self {
            circuits: Arc::new(circuit_tree),
        })
    }

    /// Returns the program ID.
    fn program_id(&self) -> &MerkleTreeDigest<C::ProgramCircuitTreeParameters> {
        self.circuits.to_program_id()
    }

    /// Returns `true` if the given circuit ID exists in the program.
    fn contains_circuit(&self, circuit_id: &C::ProgramCircuitID) -> bool {
        self.circuits.contains_circuit(circuit_id)
    }

    /// Returns the circuit given the circuit ID, if it exists.
    fn get_circuit(&self, circuit_id: &C::ProgramCircuitID) -> Option<&Box<dyn ProgramCircuit<C>>> {
        self.circuits.get_circuit(circuit_id)
    }

    /// Returns the circuit given the circuit index, if it exists.
    fn find_circuit_by_index(&self, circuit_index: u8) -> Option<&Box<dyn ProgramCircuit<C>>> {
        self.circuits.find_circuit_by_index(circuit_index)
    }

    fn execute(
        &self,
        circuit_id: &C::ProgramCircuitID,
        public: &PublicVariables<C>,
        private: &dyn PrivateVariables<C>,
    ) -> Result<Execution<C>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuits.get_circuit(circuit_id) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeaf(format!("{}", circuit_id)).into()),
        };
        debug_assert_eq!(circuit.circuit_id(), circuit_id);

        let program_path = self.circuits.get_program_path(circuit_id)?;
        debug_assert!(program_path.verify(self.program_id(), circuit_id)?);

        let proof = circuit.execute(public, private)?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Execution {
            program_path,
            verifying_key,
            proof,
        })
    }

    fn execute_blank(&self, circuit_id: &C::ProgramCircuitID) -> Result<Execution<C>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuits.get_circuit(circuit_id) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeaf(format!("{}", circuit_id)).into()),
        };
        debug_assert_eq!(circuit.circuit_id(), circuit_id);

        let program_path = self.circuits.get_program_path(circuit_id)?;
        debug_assert!(program_path.verify(self.program_id(), circuit_id)?);

        let proof = circuit.execute_blank()?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Execution {
            program_path,
            verifying_key,
            proof,
        })
    }
}
