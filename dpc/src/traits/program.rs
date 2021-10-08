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

use crate::{Executable, Execution, Function, FunctionType, Network, ProgramError, PublicVariables};
use snarkvm_algorithms::merkle_tree::MerklePath;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use anyhow::Result;

pub trait ProgramScheme<N: Network>: Send + Sync {
    /// Initializes an instance of the program with the given circuits.
    fn new(circuits: Vec<Function<N>>) -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Initializes an instance of the noop program.
    fn new_noop() -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Returns the program ID.
    fn program_id(&self) -> N::ProgramID;

    /// Returns `true` if the given function ID exists in the program.
    fn contains_function(&self, function_id: &N::FunctionID) -> bool;

    /// Returns the circuit given the function ID, if it exists.
    fn to_function(&self, function_id: &N::FunctionID) -> Option<&Function<N>>;

    /// Returns the program path (the Merkle path for a given function ID).
    fn to_program_path(
        &self,
        function_id: &N::FunctionID,
    ) -> Result<MerklePath<N::ProgramFunctionsTreeParameters>, ProgramError>;

    /// Returns an instance of an executable given the function ID, if it exists.
    fn to_executable(&self, function_id: &N::FunctionID) -> Result<Executable<N>, ProgramError>;
}

pub trait ProgramExecutable<N: Network>: Send + Sync {
    /// Initializes a new instance of an executable.
    fn new(
        program_id: N::ProgramID,
        circuit: Function<N>,
        program_path: MerklePath<N::ProgramFunctionsTreeParameters>,
    ) -> Result<Self, ProgramError>
    where
        Self: Sized;

    /// Returns the program ID of the executable.
    fn program_id(&self) -> N::ProgramID;

    /// Returns the circuit type of the executable.
    fn function_type(&self) -> FunctionType;

    /// Executes the circuit, returning an proof.
    fn execute(&self, public: PublicVariables<N>) -> Result<Execution<N>, ProgramError>;
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
    fn function_type(&self) -> FunctionType;

    /// Synthesizes the circuit inside the given constraint system.
    fn synthesize<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
        public: &PublicVariables<N>,
    ) -> Result<(), SynthesisError>
    where
        Self: Sized;
}
