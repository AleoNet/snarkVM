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
    Program,
    ProgramCircuit,
    ProgramCircuitTree,
    ProgramError,
    ProgramPublicVariables,
};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, prelude::*};

use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(Debug(bound = "C: Parameters"))]
pub struct NoopProgram<C: Parameters> {
    circuit_tree: ProgramCircuitTree<C>,
}

impl<C: Parameters> Program<C> for NoopProgram<C> {
    /// Initializes a new instance of the program.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, ProgramError> {
        // Initialize a new program circuit tree, and add all circuits to the tree.
        let mut circuit_tree = ProgramCircuitTree::new()?;
        circuit_tree.add_all(vec![Box::new(NoopCircuit::setup(rng)?)])?;

        Ok(Self { circuit_tree })
    }

    /// Loads an instance of the program.
    fn load() -> Result<Self, ProgramError> {
        // Initialize a new program circuit tree, and add all circuits to the tree.
        let mut circuit_tree = ProgramCircuitTree::new()?;
        circuit_tree.add(Box::new(NoopCircuit::load()?))?;

        Ok(Self { circuit_tree })
    }

    /// Returns the program ID.
    fn program_id(&self) -> &MerkleTreeDigest<C::ProgramIDTreeParameters> {
        self.circuit_tree.to_program_id()
    }

    fn get_circuit(&self, circuit_index: u8) -> Result<&Box<dyn ProgramCircuit<C>>, ProgramError> {
        // Fetch the circuit from the tree.
        match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => Ok(circuit),
            _ => Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        }
    }

    fn execute(
        &self,
        circuit_index: u8,
        public: &ProgramPublicVariables<C>,
        private: &(),
    ) -> Result<Execution<C>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        };
        let program_path = self.circuit_tree.get_program_path(circuit_index)?;
        let proof = circuit.execute(public, private)?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Execution {
            circuit_index,
            program_path,
            verifying_key,
            proof,
        })
    }

    fn execute_blank(&self, circuit_index: u8) -> Result<Execution<C>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        };
        let program_path = self.circuit_tree.get_program_path(circuit_index)?;
        let proof = circuit.execute_blank()?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Execution {
            circuit_index,
            program_path,
            verifying_key,
            proof,
        })
    }
}
