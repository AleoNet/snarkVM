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

use crate::{CircuitType, Execution, LocalData, Network, PrivateVariables, ProgramScheme, PublicVariables};

use anyhow::Result;
use std::{ops::Deref, sync::Arc};

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub enum Executable<N: Network> {
    Noop,
    Circuit(
        Arc<dyn ProgramScheme<N>>,
        N::ProgramCircuitID,
        Arc<dyn PrivateVariables<N>>,
    ),
}

impl<N: Network> Executable<N> {
    /// Returns `true` if the executable is a noop.
    pub fn is_noop(&self) -> bool {
        match self {
            Self::Noop => true,
            _ => false,
        }
    }

    /// Returns a reference to the program ID of the executable.
    pub fn program_id(&self) -> N::ProgramID {
        match self {
            Self::Noop => N::noop_program_id(),
            Self::Circuit(program, _, _) => program.program_id(),
        }
    }

    /// Returns the circuit type of the executable.
    pub fn circuit_type(&self) -> Result<CircuitType> {
        match self {
            Self::Noop => Ok(CircuitType::Noop),
            Self::Circuit(program, circuit_id, _) => Ok(program.get_circuit_type(circuit_id)?),
        }
    }

    /// Returns the execution of the executable given the public variables.
    pub fn execute(&self, record_position: u8, local_data: &LocalData<N>) -> Result<Execution<N>> {
        // Construct the public variables.
        let public_variables = PublicVariables::new(record_position, local_data.root());
        // Execute the program circuit with the declared variables.
        match self {
            Self::Noop => Ok(N::noop_program().execute_noop(&public_variables)?),
            Self::Circuit(program, circuit_id, private_variables) => {
                Ok(program.execute(circuit_id, &public_variables, private_variables.deref())?)
            }
        }
    }
}
