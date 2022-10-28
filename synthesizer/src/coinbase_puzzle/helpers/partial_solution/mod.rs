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
use snarkvm_algorithms::crypto_hash::sha256d_to_u64;

/// The partial solution for the coinbase puzzle from a prover.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct PartialSolution<N: Network> {
    /// The address of the prover.
    address: Address<N>,
    /// The nonce for the solution.
    nonce: u64,
    /// The commitment for the solution.
    commitment: PuzzleCommitment<N>,
}

impl<N: Network> PartialSolution<N> {
    /// Initializes a new instance of the partial solution.
    pub fn new<C: Into<PuzzleCommitment<N>>>(address: Address<N>, nonce: u64, commitment: C) -> Self {
        Self { address, nonce, commitment: commitment.into() }
    }

    /// Returns the address of the prover.
    pub const fn address(&self) -> Address<N> {
        self.address
    }

    /// Returns the nonce for the solution.
    pub const fn nonce(&self) -> u64 {
        self.nonce
    }

    /// Returns the commitment for the solution.
    pub const fn commitment(&self) -> PuzzleCommitment<N> {
        self.commitment
    }

    /// Returns the prover polynomial.
    pub fn to_prover_polynomial(
        &self,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>> {
        CoinbasePuzzle::prover_polynomial(epoch_challenge, self.address(), self.nonce())
    }

    /// Returns the target of the solution.
    pub fn to_target(&self) -> Result<u64> {
        let hash_to_u64 = sha256d_to_u64(&self.commitment.to_bytes_le()?);
        if hash_to_u64 == 0 { Ok(u64::MAX) } else { Ok(u64::MAX / hash_to_u64) }
    }
}
