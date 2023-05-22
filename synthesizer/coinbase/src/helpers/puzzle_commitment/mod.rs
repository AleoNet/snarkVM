// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
