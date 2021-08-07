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

use crate::{NoopCircuit, Parameters, Program, ProgramCircuit, ProgramError, ProgramScheme};

use rand::{CryptoRng, Rng};
use std::ops::Deref;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
pub struct NoopProgram<C: Parameters>(Program<C>);

impl<C: Parameters> NoopProgram<C> {
    /// Initializes a new instance of the program.
    pub fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, ProgramError> {
        Ok(Self(Program::new(vec![Box::new(NoopCircuit::setup(rng)?)])?))
    }

    /// Loads an instance of the program.
    pub fn load() -> Result<Self, ProgramError> {
        Ok(Self(Program::new(vec![Box::new(NoopCircuit::load()?)])?))
    }
}

impl<C: Parameters> Deref for NoopProgram<C> {
    type Target = Program<C>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
