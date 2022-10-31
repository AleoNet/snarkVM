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

use console::{network::prelude::*, types::Field};

type Variant = u16;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Origin<N: Network> {
    /// The origin is a commitment.
    Commitment(Field<N>),
    /// The origin is a global state root.
    StateRoot(N::StateRoot),
}

impl<N: Network> Origin<N> {
    /// Returns the verifier inputs for the state path proof.
    pub fn verifier_inputs(&self, serial_number: &Field<N>) -> Vec<N::Field> {
        match self {
            Self::Commitment(_) => vec![],
            Self::StateRoot(global_state_root) => {
                vec![N::Field::one(), ***global_state_root, N::Field::zero(), **serial_number]
            }
        }
    }
}
