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

/// The prover solution for the coinbase puzzle from a prover.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct ProverSolution<N: Network> {
    /// The core data of the prover solution.
    partial_solution: PartialSolution<N>,
    /// The proof for the solution.
    proof: PuzzleProof<N>,
}

impl<N: Network> ProverSolution<N> {
    /// Initializes a new instance of the prover solution.
    pub const fn new(partial_solution: PartialSolution<N>, proof: PuzzleProof<N>) -> Self {
        Self { partial_solution, proof }
    }

    /// Returns `true` if the prover solution is valid.
    pub fn verify(
        &self,
        verifying_key: &CoinbaseVerifyingKey<N>,
        epoch_challenge: &EpochChallenge<N>,
        proof_target: u64,
    ) -> Result<bool> {
        // Ensure the proof is non-hiding.
        if self.proof.is_hiding() {
            return Ok(false);
        }

        // Ensure that the prover solution is greater than the proof target.
        if self.to_target()? < proof_target {
            bail!("Prover puzzle does not meet the proof target requirements.")
        }

        // Compute the prover polynomial.
        let prover_polynomial = self.partial_solution.to_prover_polynomial(epoch_challenge)?;

        // Compute the challenge point.
        let challenge_point = hash_commitment(&self.commitment())?;

        // Evaluate the epoch and prover polynomials at the challenge point.
        let epoch_evaluation = epoch_challenge.epoch_polynomial().evaluate(challenge_point);
        let prover_evaluation = prover_polynomial.evaluate(challenge_point);

        // Compute the claimed value by multiplying the evaluations.
        let claimed_value = epoch_evaluation * prover_evaluation;

        // Check the KZG proof.
        Ok(KZG10::check(verifying_key, &self.commitment(), challenge_point, claimed_value, self.proof())?)
    }

    /// Returns the address of the prover.
    pub const fn address(&self) -> Address<N> {
        self.partial_solution.address()
    }

    /// Returns the nonce for the solution.
    pub const fn nonce(&self) -> u64 {
        self.partial_solution.nonce()
    }

    /// Returns the commitment for the solution.
    pub const fn commitment(&self) -> PuzzleCommitment<N> {
        self.partial_solution.commitment()
    }

    /// Returns the proof for the solution.
    pub const fn proof(&self) -> &PuzzleProof<N> {
        &self.proof
    }

    /// Returns the prover polynomial.
    pub fn to_prover_polynomial(
        &self,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>> {
        self.partial_solution.to_prover_polynomial(epoch_challenge)
    }

    /// Returns the target of the solution.
    pub fn to_target(&self) -> Result<u64> {
        self.partial_solution.to_target()
    }
}
