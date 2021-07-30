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
    CircuitError,
    CircuitScheme,
    CircuitTree,
    Execution,
    LocalData,
    NoopCircuit,
    Parameters,
    ProgramError,
    ProgramPublicVariables,
    ProgramScheme,
    RecordScheme,
};
use snarkvm_algorithms::prelude::*;
use snarkvm_r1cs::ToConstraintField;
use snarkvm_utilities::ToBytes;

use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
pub struct NoopProgram<C: Parameters> {
    circuit_tree: CircuitTree<C>,
}

impl<C: Parameters> ProgramScheme for NoopProgram<C> {
    type Execution = Execution<Self::ProofSystem>;
    type PrivateVariables = ();
    type ProgramID = Vec<u8>;
    type PublicVariables = ProgramPublicVariables<C>;

    /// Initializes a new instance of the program.
    fn setup(circuits: &[Box<dyn CircuitScheme>]) -> Result<Self, ProgramError> {
        // Initialize a new circuit tree, and add all circuits to the tree.
        let mut circuit_tree = CircuitTree::new()?;
        circuit_tree.add_all(circuits)?;

        Ok(Self { circuit_tree })
    }

    /// Loads an instance of the program.
    fn load() -> Result<Self, ProgramError> {
        Self::setup(&[NoopCircuit::load()?])
    }

    /// Returns the program ID.
    fn program_id(&self) -> Self::ProgramID {
        self.circuit_tree.to_program_id()
    }

    fn execute<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        public: Self::PublicVariables,
        private: Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<Self::Execution, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => circuit,
            _ => Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        };

        let proof = circuit.execute(public, private, rng)?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Self::Execution {
            circuit_index,
            verifying_key,
            proof,
        })
    }

    fn execute_blank<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        rng: &mut R,
    ) -> Result<Self::Execution, ProgramError> {
        // Fetch the circuit from the tree.
        let circuit = match self.circuit_tree.get_circuit(circuit_index) {
            Some(circuit) => circuit,
            _ => Err(MerkleError::MissingLeafIndex(circuit_index as usize).into()),
        };

        let public = Self::PublicVariables::default();
        let private = Self::PrivateVariables::default();
        let proof = circuit.execute(public, private, rng)?;
        let verifying_key = circuit.verifying_key().clone();

        Ok(Self::Execution {
            circuit_index,
            verifying_key,
            proof,
        })
    }

    fn evaluate(&self, _predicate_index: u8, _p: &Self::PublicVariables, _w: &Self::Execution) -> bool {
        unimplemented!()
    }
}

impl<C: Parameters> NoopProgram<C> {
    #[deprecated]
    pub fn to_snark_parameters(
        &self,
    ) -> (
        <C::ProgramSNARK as SNARK>::ProvingKey,
        <C::ProgramSNARK as SNARK>::VerifyingKey,
    ) {
        (self.proving_key.clone(), self.verifying_key.clone())
    }
}
