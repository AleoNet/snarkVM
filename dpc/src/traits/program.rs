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

use crate::{CircuitError, Execution, Parameters, ProgramError, ProgramPublicVariables};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, SNARK};

use rand::{CryptoRng, Rng};

pub trait Program<C: Parameters> {
    type PrivateVariables: Default;

    /// Initializes a new instance of the program.
    fn new(circuits: &[Box<dyn ProgramCircuit<C>>]) -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Loads an instance of a program.
    fn load() -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Returns the program ID.
    fn program_id(&self) -> &MerkleTreeDigest<C::ProgramIDTreeParameters>;

    /// Returns the execution of the program.
    fn execute<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        public: &ProgramPublicVariables<C>,
        private: &Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<Execution<C::ProgramSNARK>, ProgramError>;

    /// Returns the blank execution of the program, typically used for a SNARK setup.
    fn execute_blank<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        rng: &mut R,
    ) -> Result<Execution<C::ProgramSNARK>, ProgramError>;

    /// Returns the native evaluation of the program on given public and private variables.
    fn evaluate(
        &self,
        _circuit_index: u8,
        _public: &ProgramPublicVariables<C>,
        _private: &Self::PrivateVariables,
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

    /// Returns the circuit ID.
    fn circuit_id(&self) -> &Vec<u8>;

    /// Returns the circuit proving key.
    fn proving_key(&self) -> &<C::ProgramSNARK as SNARK>::ProvingKey;

    /// Returns the circuit verifying key.
    fn verifying_key(&self) -> &<C::ProgramSNARK as SNARK>::VerifyingKey;
}

pub trait ProgramExecutable<C: Parameters>: Send + Sync {
    type PrivateVariables: Default;

    /// Returns the execution of the circuit.
    fn execute<R: Rng + CryptoRng>(
        &self,
        public: &ProgramPublicVariables<C>,
        private: &Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<<C::ProgramSNARK as SNARK>::Proof, CircuitError>;

    /// Returns true if the execution of the circuit is valid.
    fn verify<R: Rng + CryptoRng>(
        &self,
        public: &ProgramPublicVariables<C>,
        proof: <C::ProgramSNARK as SNARK>::Proof,
    ) -> bool;

    /// Returns the native evaluation of the circuit on given public and private variables.
    fn evaluate(&self, _public: &ProgramPublicVariables<C>, _private: &impl Default) -> bool {
        unimplemented!("The native evaluation of this circuit is unimplemented")
    }
}
