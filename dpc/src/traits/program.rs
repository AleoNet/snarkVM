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

use crate::{CircuitError, Execution, Parameters, ProgramError, PublicVariables};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, SNARK};

use rand::{CryptoRng, Rng};

pub trait ProgramScheme<C: Parameters>: Send + Sync {
    /// Initializes an instance of the program with the given circuits.
    fn new(circuits: Vec<Box<dyn ProgramCircuit<C>>>) -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Returns a reference to the program ID.
    fn program_id(&self) -> &MerkleTreeDigest<C::ProgramCircuitTreeParameters>;

    /// Returns `true` if the given circuit ID exists in the program.
    fn contains_circuit(&self, circuit_id: &C::ProgramCircuitID) -> bool;

    /// Returns the circuit given the circuit ID, if it exists.
    fn get_circuit(&self, circuit_id: &C::ProgramCircuitID) -> Option<&Box<dyn ProgramCircuit<C>>>;

    /// Returns the circuit given the circuit index, if it exists.
    fn find_circuit_by_index(&self, circuit_index: u8) -> Option<&Box<dyn ProgramCircuit<C>>>;

    /// Returns the execution of the program.
    fn execute(
        &self,
        circuit_id: &C::ProgramCircuitID,
        public: &PublicVariables<C>,
        private: &dyn PrivateVariables<C>,
    ) -> Result<Execution<C>, ProgramError>;

    /// Returns the blank execution of the program, typically used for a SNARK setup.
    fn execute_blank(&self, circuit_id: &C::ProgramCircuitID) -> Result<Execution<C>, ProgramError>;

    /// Returns the native evaluation of the program on given public and private variables.
    fn evaluate(
        &self,
        _circuit_id: &C::ProgramCircuitID,
        _public: &PublicVariables<C>,
        _private: &dyn PrivateVariables<C>,
    ) -> bool {
        unimplemented!("The native evaluation of this program is unimplemented")
    }
}

pub trait ProgramCircuit<C: Parameters>: Send + Sync {
    /// Initializes a new instance of a circuit.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, CircuitError>
    where
        Self: Sized;

    /// Loads an instance of a circuit.
    fn load() -> Result<Self, CircuitError>
    where
        Self: Sized;

    /// Returns the program circuit ID.
    fn circuit_id(&self) -> &C::ProgramCircuitID;

    /// Returns the circuit proving key.
    fn proving_key(&self) -> &<C::ProgramSNARK as SNARK>::ProvingKey;

    /// Returns the circuit verifying key.
    fn verifying_key(&self) -> &<C::ProgramSNARK as SNARK>::VerifyingKey;

    /// Returns the execution of the circuit.
    fn execute(
        &self,
        public: &PublicVariables<C>,
        private: &dyn PrivateVariables<C>,
    ) -> Result<<C::ProgramSNARK as SNARK>::Proof, CircuitError>;

    /// Returns the blank execution of the circuit, typically used for a SNARK setup.
    fn execute_blank(&self) -> Result<<C::ProgramSNARK as SNARK>::Proof, CircuitError>;

    /// Returns true if the execution of the circuit is valid.
    fn verify(&self, public: &PublicVariables<C>, proof: &<C::ProgramSNARK as SNARK>::Proof) -> bool;

    /// Returns the native evaluation of the circuit on given public and private variables.
    fn evaluate(&self, _public: &PublicVariables<C>, _private: &dyn PrivateVariables<C>) -> bool {
        unimplemented!("The native evaluation of this circuit is unimplemented")
    }
}

pub trait PrivateVariables<C: Parameters>: Send + Sync {
    fn as_any(&self) -> &dyn std::any::Any;
}
