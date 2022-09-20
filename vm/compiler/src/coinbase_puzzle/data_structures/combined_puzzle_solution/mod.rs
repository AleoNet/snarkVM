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
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CombinedPuzzleSolution<N: Network> {
    pub individual_puzzle_solutions: Vec<PartialProverSolution<N>>,
    pub proof: Proof<N::PairingCurve>,
}

impl<N: Network> CombinedPuzzleSolution<N> {
    pub fn new(individual_puzzle_solutions: Vec<PartialProverSolution<N>>, proof: Proof<N::PairingCurve>) -> Self {
        Self { individual_puzzle_solutions, proof }
    }

    pub fn verify(
        &self,
        vk: &CoinbasePuzzleVerifyingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<bool> {
        if self.individual_puzzle_solutions.is_empty() {
            return Ok(false);
        }
        if self.proof.is_hiding() {
            return Ok(false);
        }
        let polynomials: Vec<_> = cfg_iter!(self.individual_puzzle_solutions)
            .map(|solution| {
                // TODO: check difficulty of solution
                CoinbasePuzzle::sample_solution_polynomial(
                    epoch_challenge,
                    epoch_info,
                    solution.address(),
                    solution.nonce(),
                )
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute challenges
        let mut fs_challenges =
            hash_commitments(self.individual_puzzle_solutions.iter().map(|solution| *solution.commitment()));
        let point = match fs_challenges.pop() {
            Some(point) => point,
            None => bail!("Missing challenge point"),
        };

        // Compute combined evaluation
        let mut combined_eval = cfg_iter!(polynomials)
            .zip(&fs_challenges)
            .fold(<N::PairingCurve as PairingEngine>::Fr::zero, |acc, (poly, challenge)| {
                acc + (poly.evaluate(point) * challenge)
            })
            .sum();
        combined_eval *= &epoch_challenge.epoch_polynomial.evaluate(point);

        // Compute combined commitment
        let commitments: Vec<_> =
            cfg_iter!(self.individual_puzzle_solutions).map(|solution| solution.commitment().0).collect();
        let fs_challenges = fs_challenges.into_iter().map(|f| f.to_repr()).collect::<Vec<_>>();
        let combined_commitment = VariableBase::msm(&commitments, &fs_challenges);
        let combined_commitment: Commitment<N::PairingCurve> = Commitment(combined_commitment.into());
        Ok(KZG10::check(vk, &combined_commitment, point, combined_eval, &self.proof)?)
    }
}
