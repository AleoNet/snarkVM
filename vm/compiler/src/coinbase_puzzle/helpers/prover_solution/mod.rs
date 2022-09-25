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
    /// The core data of the prover solution.
    partial_solution: PartialSolution<N>,
    /// The proof for the solution.
    proof: KZGProof<N::PairingCurve>,
}

impl<N: Network> ProverSolution<N> {
    /// Initializes a new instance of the prover solution.
    pub fn new(partial_solution: PartialSolution<N>, proof: KZGProof<N::PairingCurve>) -> Self {
        Self { partial_solution, proof }
    }

    /// Returns `true` if the prover solution is valid.
    pub fn verify(&self, vk: &CoinbasePuzzleVerifyingKey<N>, epoch_challenge: &EpochChallenge<N>) -> Result<bool> {
        // Ensure the proof is non-hiding.
        if self.proof.is_hiding() {
            return Ok(false);
        }

        // TODO: check difficulty of solution.

        // Compute the challenge point.
        let challenge_point = hash_commitment(self.commitment());

        // Compute the prover polynomial.
        let prover_polynomial =
            CoinbasePuzzle::sample_solution_polynomial(epoch_challenge, self.address(), self.nonce())?;

        // Evaluate the epoch and prover polynomials at the challenge point.
        let epoch_evaluation = epoch_challenge.epoch_polynomial.evaluate(challenge_point);
        let prover_evaluation = prover_polynomial.evaluate(challenge_point);

        // Compute the claimed value by multiplying the evaluations.
        let claimed_value = epoch_evaluation * prover_evaluation;

        // Check the KZG proof.
        Ok(KZG10::check(vk, self.commitment(), challenge_point, claimed_value, self.proof())?)
    }

    /// Returns the address of the prover.
    pub fn address(&self) -> &Address<N> {
        self.partial_solution.address()
    }

    /// Returns the nonce for the solution.
    pub fn nonce(&self) -> u64 {
        self.partial_solution.nonce()
    }

    /// Returns the commitment for the solution.
    pub fn commitment(&self) -> &KZGCommitment<N::PairingCurve> {
        self.partial_solution.commitment()
    }

    /// Returns the proof for the solution.
    pub fn proof(&self) -> &KZGProof<N::PairingCurve> {
        &self.proof
    }

    /// Returns the difficulty target of the solution.
    pub fn to_difficulty_target(&self) -> Result<u64> {
        self.partial_solution.to_difficulty_target()
    }
}
