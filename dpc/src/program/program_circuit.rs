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

use crate::{Network, ProgramPublicVariables};
// use snarkvm_algorithms::traits::*;
// use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
// use snarkvm_utilities::ToBytes;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct ProgramCircuit<N: Network> {
    public: ProgramPublicVariables<N>,
}

impl<N: Network> ProgramCircuit<N> {
    pub fn blank() -> Self {
        Self {
            public: ProgramPublicVariables::blank(),
        }
    }

    pub fn new(public: ProgramPublicVariables<N>) -> Self {
        Self { public }
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for ProgramCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        _cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        Ok(())
    }
}
