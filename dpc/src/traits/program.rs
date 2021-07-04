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

use crate::errors::DPCError;

use core::fmt::Debug;
use rand::Rng;

pub trait ProgramScheme: Clone {
    type Id: Debug;
    type LocalData;
    type PrivateWitness;
    type ProvingKey;
    type PublicInput;
    type VerifyingKey;

    /// Initializes a new instance of a program.
    fn new(program_id: Self::Id, proving_key: Self::ProvingKey, verifying_key: Self::VerifyingKey) -> Self;

    /// Executes the program, returning the execution proof.
    fn execute<R: Rng>(
        &self,
        local_data: &Self::LocalData,
        position: u8,
        rng: &mut R,
    ) -> Result<Self::PrivateWitness, DPCError>;

    /// Returns the evaluation of the program on given input and witness.
    fn evaluate(&self, primary: &Self::PublicInput, witness: &Self::PrivateWitness) -> bool;

    /// Returns the program identity
    #[allow(clippy::wrong_self_convention)]
    fn into_compact_repr(&self) -> Vec<u8>;
}
