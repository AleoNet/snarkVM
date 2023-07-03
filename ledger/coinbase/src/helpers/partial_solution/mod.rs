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
        self.commitment.to_target()
    }
}
