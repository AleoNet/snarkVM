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

use crate::{CircuitType, Executable, Execution, LocalData, Network, ProgramCircuit, ProgramError, PublicVariables};
use snarkvm_algorithms::{merkle_tree::MerklePath, SNARK};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use anyhow::Result;

pub trait ProgramScheme<N: Network>: Send + Sync {
    /// Initializes an instance of the program with the given circuits.
    fn new(circuits: Vec<ProgramCircuit<N>>) -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Initializes an instance of the noop program.
    fn new_noop() -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Returns the program ID.
    fn program_id(&self) -> N::ProgramID;

    /// Returns `true` if the given circuit ID exists in the program.
    fn contains_circuit(&self, circuit_id: &N::ProgramCircuitID) -> bool;

    /// Returns the circuit given the circuit ID, if it exists.
    fn to_circuit(&self, circuit_id: &N::ProgramCircuitID) -> Option<&ProgramCircuit<N>>;

    /// Returns the program path (the Merkle path for a given circuit ID).
    fn to_program_path(
        &self,
        circuit_id: &N::ProgramCircuitID,
    ) -> Result<MerklePath<N::ProgramCircuitTreeParameters>, ProgramError>;

    /// Returns an instance of an executable given the circuit ID, if it exists.
    fn to_executable(&self, circuit_id: &N::ProgramCircuitID) -> Result<Executable<N>, ProgramError>;
}

pub trait ProgramExecutable<N: Network>: Send + Sync {
    /// Initializes a new instance of an executable.
    fn new(
        program_id: N::ProgramID,
        circuit: ProgramCircuit<N>,
        program_path: MerklePath<N::ProgramCircuitTreeParameters>,
    ) -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Returns the program ID of the executable.
    fn program_id(&self) -> N::ProgramID;

    /// Returns the circuit ID of the executable.
    fn circuit_id(&self) -> N::ProgramCircuitID;

    /// Returns the circuit type of the executable.
    fn circuit_type(&self) -> CircuitType;

    /// Returns the native evaluation of the executable on given public and private variables.
    fn evaluate(&self, _public: PublicVariables<N>, _local_data: &LocalData<N>) -> bool {
        unimplemented!("The native evaluation of this executable is unimplemented")
    }

    /// Executes the circuit, returning an proof.
    fn execute(&self, public: PublicVariables<N>, local_data: &LocalData<N>) -> Result<Execution<N>, ProgramError>;

    /// Returns true if the execution of the circuit is valid.
    fn verify(&self, public: PublicVariables<N>, proof: &<N::ProgramSNARK as SNARK>::Proof) -> bool;
}

pub trait PrivateVariables<N: Network>: Send + Sync {
    /// Initializes a blank instance of the private variables, typically used for a SNARK setup.
    fn new_blank() -> Result<Self>
    where
        Self: Sized;

    fn as_any(&self) -> &dyn std::any::Any;
}

pub trait CircuitLogic<N: Network>: Send + Sync {
    /// Returns the circuit type.
    fn circuit_type(&self) -> CircuitType;

    /// Synthesizes the circuit inside the given constraint system.
    fn synthesize<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
        public: &PublicVariables<N>,
    ) -> Result<(), SynthesisError>
    where
        Self: Sized;
}
