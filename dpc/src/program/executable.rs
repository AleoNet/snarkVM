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

use crate::{Execution, LocalData, NoopProgram, Parameters, PrivateVariables, ProgramScheme, PublicVariables};
use snarkvm_algorithms::merkle_tree::MerkleTreeDigest;

use anyhow::Result;
use std::{ops::Deref, sync::Arc};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub enum Executable<C: Parameters> {
    /// TODO (howardwu): TEMPORARY - `Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    Noop(Arc<NoopProgram<C>>),
    Circuit(
        Arc<dyn ProgramScheme<C>>,
        C::ProgramCircuitID,
        Arc<dyn PrivateVariables<C>>,
    ),
}

impl<C: Parameters> Executable<C> {
    /// Returns `true` if the executable is a noop.
    pub fn is_noop(&self) -> bool {
        match self {
            Self::Noop(_) => true,
            _ => false,
        }
    }

    /// Returns a reference to the program ID of the executable.
    pub fn program_id(&self) -> &MerkleTreeDigest<C::ProgramCircuitTreeParameters> {
        match self {
            Self::Noop(program) => program.program_id(),
            Self::Circuit(program, _, _) => program.program_id(),
        }
    }

    /// Returns the execution of the executable given the public variables.
    pub fn execute(&self, record_position: u8, local_data: &LocalData<C>) -> Result<Execution<C>> {
        // Construct the public variables.
        let public_variables = PublicVariables::new(record_position, local_data.root());
        // Execute the program circuit with the declared variables.
        match self {
            Self::Noop(program) => Ok(program.execute_noop(&public_variables)?),
            Self::Circuit(program, circuit_id, private_variables) => {
                Ok(program.execute(circuit_id, &public_variables, private_variables.deref())?)
            }
        }
    }

    /// Returns a reference to the executable program.
    pub fn program(&self) -> &dyn ProgramScheme<C> {
        match self {
            Self::Noop(program) => program.deref().deref(),
            Self::Circuit(program, _, _) => program.deref(),
        }
    }
}
