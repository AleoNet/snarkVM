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

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::*;

/// The coinbase puzzle solution constructed by accumulating the individual prover solutions.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct CoinbaseSolution<N: Network> {
    pub partial_solutions: Vec<PartialSolution<N>>,
    pub proof: KZGProof<N::PairingCurve>,
}

impl<N: Network> CoinbaseSolution<N> {
    /// Initializes a new instance of a coinbase solution.
    pub const fn new(partial_solutions: Vec<PartialSolution<N>>, proof: KZGProof<N::PairingCurve>) -> Self {
        Self { partial_solutions, proof }
    }

    pub fn verify(&self, verifying_key: &CoinbaseVerifyingKey<N>, epoch_challenge: &EpochChallenge<N>) -> Result<bool> {
        // Ensure the solution is not empty.
        if self.partial_solutions.is_empty() {
            return Ok(false);
        }

        // Ensure the proof is non-hiding.
        if self.proof.is_hiding() {
            return Ok(false);
        }

        // Compute the prover polynomials.
        let prover_polynomials: Vec<_> = cfg_iter!(self.partial_solutions)
            .map(|solution| {
                // TODO: check difficulty of solution
                solution.to_prover_polynomial(epoch_challenge)
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute the challenge points.
        let mut challenge_points =
            hash_commitments::<N>(self.partial_solutions.iter().map(|solution| *solution.commitment()))?;
        ensure!(challenge_points.len() == self.partial_solutions.len() + 1, "Invalid number of challenge points");

        // Pop the last challenge point as the accumulator challenge point.
        let accumulator_point = match challenge_points.pop() {
            Some(point) => point,
            None => bail!("Missing the accumulator challenge point"),
        };

        // Compute the accumulator evaluation.
        let mut accumulator_evaluation = cfg_iter!(prover_polynomials)
            .zip(&challenge_points)
            .fold(<N::PairingCurve as PairingEngine>::Fr::zero, |accumulator, (prover_polynomial, challenge_point)| {
                accumulator + (prover_polynomial.evaluate(accumulator_point) * challenge_point)
            })
            .sum();
        accumulator_evaluation *= &epoch_challenge.epoch_polynomial().evaluate(accumulator_point);

        // Compute the accumulator commitment.
        let commitments: Vec<_> = cfg_iter!(self.partial_solutions).map(|solution| solution.commitment().0).collect();
        let fs_challenges = challenge_points.into_iter().map(|f| f.to_repr()).collect::<Vec<_>>();
        let accumulator_commitment =
            KZGCommitment::<N::PairingCurve>(VariableBase::msm(&commitments, &fs_challenges).into());

        // Return the verification result.
        Ok(KZG10::check(
            verifying_key,
            &accumulator_commitment,
            accumulator_point,
            accumulator_evaluation,
            &self.proof,
        )?)
    }

    /// Returns the cumulative difficulty of the individual prover solutions.
    /// NOTE that this is NOT the cumulative difficulty target of the individual prover solutions.
    pub fn to_cumulative_difficulty(&self) -> Result<u64> {
        let mut cumulative_difficulty: u64 = 0;

        for solution in &self.partial_solutions {
            let solution_difficulty = u64::MAX.saturating_div(solution.to_difficulty_target()?);
            cumulative_difficulty = cumulative_difficulty.saturating_add(solution_difficulty);
        }

        Ok(cumulative_difficulty)
    }
}
