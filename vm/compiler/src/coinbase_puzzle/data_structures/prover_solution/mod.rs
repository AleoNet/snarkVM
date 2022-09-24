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

/// The prover solution for the coinbase puzzle from a prover.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct ProverSolution<N: Network> {
    partial_solution: PartialSolution<N>,
    proof: KZGProof<N::PairingCurve>,
}

impl<N: Network> ProverSolution<N> {
    pub fn new(partial_solution: PartialSolution<N>, proof: KZGProof<N::PairingCurve>) -> Self {
        Self { partial_solution, proof }
    }

    pub fn verify(
        &self,
        vk: &CoinbasePuzzleVerifyingKey<N>,
        epoch_info: &EpochInfo<N>,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<bool> {
        if self.proof.is_hiding() {
            return Ok(false);
        }

        let polynomial =
            CoinbasePuzzle::sample_solution_polynomial(epoch_challenge, epoch_info, self.address(), self.nonce())?;
        let point = hash_commitment(self.commitment());
        let epoch_challenge_eval = epoch_challenge.epoch_polynomial.evaluate(point);
        let polynomial_eval = polynomial.evaluate(point);
        let product_eval = epoch_challenge_eval * polynomial_eval;
        Ok(KZG10::check(vk, self.commitment(), point, product_eval, self.proof())?)
    }

    pub fn address(&self) -> &Address<N> {
        self.partial_solution.address()
    }

    pub fn nonce(&self) -> u64 {
        self.partial_solution.nonce()
    }

    pub fn commitment(&self) -> &KZGCommitment<N::PairingCurve> {
        self.partial_solution.commitment()
    }

    pub fn proof(&self) -> &KZGProof<N::PairingCurve> {
        &self.proof
    }

    /// Returns the difficulty target of the prover solution.
    pub fn to_difficulty_target(&self) -> Result<u64> {
        self.partial_solution.to_difficulty_target()
    }
}
