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
    CircuitTree,
    Execution,
    NoopCircuit,
    Parameters,
    Program,
    ProgramCircuit,
    ProgramError,
    ProgramPublicVariables,
};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, prelude::*};

use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(Debug(bound = "C: Parameters"))]
pub struct NoopProgram<C: Parameters> {
    circuit_tree: CircuitTree<C>,
}

impl<C: Parameters> Program<C> for NoopProgram<C> {
    type PrivateVariables = ();

    /// Initializes a new instance of the program.
    fn new(circuits: &[Box<dyn ProgramCircuit<C>>]) -> Result<Self, ProgramError> {
        // Initialize a new circuit tree, and add all circuits to the tree.
        let mut circuit_tree = CircuitTree::new()?;
        circuit_tree.add_all(circuits)?;

        Ok(Self { circuit_tree })
    }

    /// Loads an instance of the program.
    fn load() -> Result<Self, ProgramError> {
        Self::new(&[Box::new(NoopCircuit::load()?)])
    }

    /// Returns the program ID.
    fn program_id(&self) -> &MerkleTreeDigest<C::ProgramIDTreeParameters> {
        self.circuit_tree.to_program_id()
    }

    fn execute<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        public: &ProgramPublicVariables<C>,
        private: &Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<Execution<C::ProgramSNARK>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        };

        let proof = circuit.execute(public, private, rng)?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Execution {
            circuit_index,
            verifying_key,
            proof,
        })
    }

    fn execute_blank<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        rng: &mut R,
    ) -> Result<Execution<C::ProgramSNARK>, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => circuit,
            _ => return Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        };

        let public = ProgramPublicVariables::<C>::default();
        let private = Self::PrivateVariables::default();
        let proof = circuit.execute(public, private, rng)?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Execution {
            circuit_index,
            verifying_key,
            proof,
        })
    }
}
