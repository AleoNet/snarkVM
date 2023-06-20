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
use snarkvm_algorithms::crypto_hash::sha256d_to_u64;

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

    /// Initializes a new instance of the puzzle commitment.
    pub fn from_g1_affine(commitment: <<N as Environment>::PairingCurve as PairingEngine>::G1Affine) -> Self {
        Self::from(KZGCommitment(commitment))
    }

    /// Returns the proof target.
    pub fn to_target(&self) -> Result<u64> {
        let hash_to_u64 = sha256d_to_u64(&self.commitment.to_bytes_le()?);
        if hash_to_u64 == 0 { Ok(u64::MAX) } else { Ok(u64::MAX / hash_to_u64) }
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
