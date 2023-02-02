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

use super::*;

/// A coinbase puzzle commitment to a polynomial.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct PuzzleCommitment<N: Network> {
    /// The commitment for the solution.
    commitment: KZGCommitment<<N as Environment>::PairingCurve>,
}

impl<N: Network> PuzzleCommitment<N> {
    /// Initializes a new instance of the puzzle commitment.
    pub const fn new(commitment: KZGCommitment<<N as Environment>::PairingCurve>) -> Self {
        Self { commitment }
    }
}

impl<N: Network> From<KZGCommitment<<N as Environment>::PairingCurve>> for PuzzleCommitment<N> {
    /// Initializes a new instance of the puzzle commitment.
    fn from(commitment: KZGCommitment<<N as Environment>::PairingCurve>) -> Self {
        Self::new(commitment)
    }
}

impl<N: Network> Default for PuzzleCommitment<N> {
    fn default() -> Self {
        Self::new(KZGCommitment::empty())
    }
}

impl<N: Network> Deref for PuzzleCommitment<N> {
    type Target = KZGCommitment<<N as Environment>::PairingCurve>;

    fn deref(&self) -> &Self::Target {
        &self.commitment
    }
}
