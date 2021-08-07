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
    NoopCircuit,
    NoopPrivateVariables,
    Parameters,
    Program,
    ProgramCircuit,
    ProgramError,
    ProgramScheme,
    PublicVariables,
};

use rand::{CryptoRng, Rng};
use std::ops::Deref;

/// As there is only one circuit in a noop program, this struct explicitly stores
/// the noop circuit ID and provides a convenience method to execute the noop circuit directly.
#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
pub struct NoopProgram<C: Parameters> {
    program: Program<C>,
    noop_circuit_id: C::ProgramCircuitID,
}

impl<C: Parameters> NoopProgram<C> {
    /// Initializes a new instance of the program.
    pub fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, ProgramError> {
        let noop_circuit = NoopCircuit::setup(rng)?;
        let noop_circuit_id = *noop_circuit.circuit_id();
        Ok(Self::from((
            Program::new(vec![Box::new(noop_circuit)])?,
            noop_circuit_id,
        )))
    }

    /// Loads an instance of the program.
    pub fn load() -> Result<Self, ProgramError> {
        let noop_circuit = NoopCircuit::load()?;
        let noop_circuit_id = *noop_circuit.circuit_id();
        Ok(Self::from((
            Program::new(vec![Box::new(noop_circuit)])?,
            noop_circuit_id,
        )))
    }

    /// Returns the noop execution with the given public variables.
    pub fn execute_noop(&self, public: &PublicVariables<C>) -> Result<Execution<C>, ProgramError> {
        debug_assert!(self.program.contains_circuit(&self.noop_circuit_id));
        Ok(self
            .program
            .execute(&self.noop_circuit_id, &public, &NoopPrivateVariables::new())?)
    }

    /// Returns a blank noop execution.
    pub fn execute_blank_noop(&self) -> Result<Execution<C>, ProgramError> {
        debug_assert!(self.program.contains_circuit(&self.noop_circuit_id));
        Ok(self.program.execute_blank(&self.noop_circuit_id)?)
    }
}

impl<C: Parameters> From<(Program<C>, C::ProgramCircuitID)> for NoopProgram<C> {
    fn from((program, noop_circuit_id): (Program<C>, C::ProgramCircuitID)) -> Self {
        debug_assert!(program.contains_circuit(&noop_circuit_id));
        Self {
            program,
            noop_circuit_id,
        }
    }
}

impl<C: Parameters> Deref for NoopProgram<C> {
    type Target = Program<C>;

    fn deref(&self) -> &Self::Target {
        &self.program
    }
}
