// Copyright (C) 2019-2022 Aleo Systems Inc.
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
use snarkvm_r1cs::{ConstraintSystem, SynthesisError, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::fmt::Debug;

pub trait Function<N: Network>: Send + Sync {
    /// Returns the function ID.
    fn function_id(&self) -> N::FunctionID;

    /// Executes the function, returning an proof.
    fn execute(
        &self,
        public: ProgramPublicVariables<N>,
        private: &dyn ProgramPrivateVariables<N>,
    ) -> Result<N::ProgramProof>;

    /// Returns true if the execution of the function is valid.
    fn verify(&self, public: &ProgramPublicVariables<N>, proof: &N::ProgramProof) -> bool;

    /// Synthesizes the circuit inside the given constraint system.
    fn synthesize<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
        public: &ProgramPublicVariables<N>,
    ) -> Result<(), SynthesisError>
    where
        Self: Sized;
}

pub trait ProgramPrivateVariables<N: Network>:
    ToConstraintField<N::InnerScalarField> + Debug + ToBytes + FromBytes + Send + Sync
{
    /// Initializes a blank instance of the private variables, typically used for a SNARK setup.
    fn new_blank() -> Result<Self>
    where
        Self: Sized;

    fn as_any(&self) -> &dyn std::any::Any;
}
