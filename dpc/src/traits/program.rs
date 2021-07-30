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

use crate::errors::{CircuitError, ProgramError};
use snarkvm_algorithms::SNARK;

use core::fmt::Debug;
use rand::{CryptoRng, Rng};

pub trait CircuitScheme: Clone {
    type CircuitID: Debug;

    type ProvingKey;
    type VerifyingKey;
    type Proof;

    type PublicVariables: Default;
    type PrivateVariables: Default;

    /// Initializes a new instance of a circuit.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, CircuitError>;

    /// Loads an instance of a circuit.
    fn load() -> Result<Self, CircuitError>;

    /// Returns the circuit ID.
    fn circuit_id(&self) -> &Self::CircuitID;

    /// Returns the circuit proving key.
    fn proving_key(&self) -> &Self::ProvingKey;

    /// Returns the circuit verifying key.
    fn verifying_key(&self) -> &Self::VerifyingKey;

    /// Returns the execution of the circuit.
    fn execute<R: Rng + CryptoRng>(
        &self,
        public: Self::PublicVariables,
        private: Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<Self::Proof, CircuitError>;

    /// Returns the native evaluation of the circuit on given public and private variables.
    fn evaluate(&self, _public: &Self::PublicVariables, _private: &Self::PrivateVariables) -> bool {
        unimplemented!("The native evaluation of this circuit is unimplemented")
    }
}

pub trait ProgramScheme: Clone {
    type ProgramID: Debug;

    type Execution;
    type PublicVariables: Default;
    type PrivateVariables: Default;

    /// Initializes a new instance of the program.
    fn setup(circuits: &[Box<dyn CircuitScheme>]) -> Result<Self, ProgramError>;

    /// Loads an instance of a program.
    fn load() -> Result<Self, ProgramError>;

    /// Returns the program ID.
    fn program_id(&self) -> &Self::ProgramID;

    /// Returns the execution of the program.
    fn execute<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        public: Self::PublicVariables,
        private: Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<Self::Execution, ProgramError>;

    /// Returns the blank execution of the program, typically used for a SNARK setup.
    fn execute_blank<R: Rng + CryptoRng>(
        &self,
        circuit_index: u8,
        rng: &mut R,
    ) -> Result<Self::Execution, ProgramError>;

    /// Returns the evaluation of the program on given input and witness.
    fn evaluate(&self, _circuit_index: u8, _primary: &Self::PublicInput, _witness: &Self::Execution) -> bool {
        unimplemented!("The native evaluation of this program is unimplemented")
    }
}
