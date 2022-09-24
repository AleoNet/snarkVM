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

/// The partial prover solution for the coinbase puzzle.
#[derive(Copy, Clone)]
pub struct PartialProverSolution<N: Network> {
    pub address: Address<N>,
    pub nonce: u64,
    pub commitment: PolynomialCommitment<N::PairingCurve>,
}

impl<N: Network> PartialProverSolution<N> {
    pub fn new(address: Address<N>, nonce: u64, commitment: PolynomialCommitment<N::PairingCurve>) -> Self {
        Self { address, nonce, commitment }
    }

    pub fn address(&self) -> &Address<N> {
        &self.address
    }

    pub fn nonce(&self) -> u64 {
        self.nonce
    }

    pub fn commitment(&self) -> &PolynomialCommitment<N::PairingCurve> {
        &self.commitment
    }

    /// Returns the difficulty target of the prover solution.
    pub fn to_difficulty_target(&self) -> Result<u64> {
        Ok(sha256d_to_u64(&self.commitment.to_bytes_le()?))
    }
}

impl<N: Network> Eq for PartialProverSolution<N> {}

impl<N: Network> PartialEq for PartialProverSolution<N> {
    /// Implements the `Eq` trait for the PartialProverSolution.
    fn eq(&self, other: &Self) -> bool {
        self.address == other.address && self.nonce == other.nonce && self.commitment == other.commitment
    }
}

// TODO (raychu86): Use derive Hash. It seems commitment and proof do not derive it properly.
impl<N: Network> core::hash::Hash for PartialProverSolution<N> {
    /// Implements the `Hash` trait for the PartialProverSolution.
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.address.hash(state);
        self.nonce.hash(state);
        self.commitment.0.hash(state);
    }
}
