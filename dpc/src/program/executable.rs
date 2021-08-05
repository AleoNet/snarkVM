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
    LocalData,
    NoopPrivateVariables,
    Parameters,
    Program,
    ProgramPrivateVariables,
    ProgramPublicVariables,
};

use anyhow::Result;
use std::{ops::Deref, sync::Arc};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub enum Executable<C: Parameters> {
    Noop(Arc<dyn Program<C>>, C::ProgramCircuitID),
    Circuit(
        Arc<dyn Program<C>>,
        C::ProgramCircuitID,
        Arc<dyn ProgramPrivateVariables<C>>,
    ),
}

impl<C: Parameters> Executable<C> {
    pub fn execute(&self, record_position: u8, local_data: &LocalData<C>) -> Result<Execution<C>> {
        // Construct the public variables.
        let public_variables = ProgramPublicVariables::new(record_position, local_data.root());
        // Execute the program circuit with the declared private variables.
        match self {
            Self::Noop(program, circuit_id) => {
                Ok(program.execute(circuit_id, &public_variables, &NoopPrivateVariables::new())?)
            }
            Self::Circuit(program, circuit_id, private_variables) => {
                Ok(program.execute(circuit_id, &public_variables, private_variables.deref())?)
            }
        }
    }
}
