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

mod bytes;
mod serialize;
mod string;

use crate::Proof;
use console::network::prelude::*;

type Variant = u8;

/// The transition output.
#[derive(Clone, PartialEq, Eq)]
pub enum TransitionProof<N: Network> {
    /// A transition that does not consume records.
    Birth(Proof<N>),
    /// A transition that consumes records.
    BirthAndDeath { execution_proof: Proof<N>, state_path_proof: Proof<N> },
}

impl<N: Network> TransitionProof<N> {
    /// Initializes a new transition proof.
    pub const fn new_birth(execution: Proof<N>) -> Self {
        Self::Birth(execution)
    }

    /// Initializes a new transition proof.
    pub const fn new_birth_and_death(execution: Proof<N>, state_path: Proof<N>) -> Self {
        Self::BirthAndDeath { execution_proof: execution, state_path_proof: state_path }
    }
}
