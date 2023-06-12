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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
#![warn(clippy::cast_possible_truncation)]

mod helpers;
pub use helpers::*;

mod hash;
use hash::*;

#[cfg(test)]
mod tests;

use console::{
    account::Address,
    prelude::{anyhow, bail, cfg_iter, ensure, has_duplicates, Network, Result, ToBytes},
    program::cfg_into_iter,
};
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    msm::VariableBase,
    polycommit::kzg10::{KZGCommitment, UniversalParams as SRS, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_synthesizer_snark::UniversalSRS;
use snarkvm_utilities::cfg_zip_fold;

use std::sync::Arc;

#[cfg(feature = "serial")]
use itertools::Itertools;
#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

#[derive(Clone)]
pub enum CoinbasePuzzle<N: Network> {
    /// The prover contains the coinbase puzzle proving key.
    Prover(Arc<CoinbaseProvingKey<N>>),
    /// The verifier contains the coinbase puzzle verifying key.
    Verifier(Arc<CoinbaseVerifyingKey<N>>),
}

impl<N: Network> CoinbasePuzzle<N> {
    /// Initializes a new `SRS` for the coinbase puzzle.
    #[cfg(any(test, feature = "setup"))]
    pub fn setup(config: PuzzleConfig) -> Result<SRS<N::PairingCurve>> {
        // The SRS must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        let total_degree = (2 * config.degree - 1).try_into()?;
        let srs = KZG10::load_srs(total_degree)?;
        Ok(srs)
    }

    /// Load the coinbase puzzle proving and verifying keys.
    pub fn load() -> Result<Self> {
        let max_degree = N::COINBASE_PUZZLE_DEGREE;
        // Load the universal SRS.
        let universal_srs = UniversalSRS::<N>::load()?;
        // Trim the universal SRS to the maximum degree.
        Self::trim(&*universal_srs, PuzzleConfig { degree: max_degree })
    }

    pub fn trim(srs: &SRS<N::PairingCurve>, config: PuzzleConfig) -> Result<Self> {
        // As above, we must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        // Since the upper bound to `srs.powers_of_beta_g` takes as input the number
        // of coefficients. The degree of the product has `2n - 1` coefficients.
        //
        // Hence, we request the powers of beta for the interval [0, 2n].
        let product_domain = Self::product_domain(config.degree)?;

        let lagrange_basis_at_beta_g = srs.lagrange_basis(product_domain)?;
        let fft_precomputation = product_domain.precompute_fft();
        let product_domain_elements = product_domain.elements().collect();

        let vk = CoinbaseVerifyingKey::<N> {
            g: srs.power_of_beta_g(0)?,
            gamma_g: <N::PairingCurve as PairingEngine>::G1Affine::zero(), // We don't use gamma_g later on since we are not hiding.
            h: srs.h,
            beta_h: srs.beta_h(),
            prepared_h: srs.prepared_h.clone(),
            prepared_beta_h: srs.prepared_beta_h.clone(),
        };

        let pk = CoinbaseProvingKey {
            product_domain,
            product_domain_elements,
            lagrange_basis_at_beta_g,
            fft_precomputation,
            verifying_key: vk,
        };

        Ok(Self::Prover(Arc::new(pk)))
    }

    /// Returns a prover solution to the coinbase puzzle.
    pub fn prove(
        &self,
        epoch_challenge: &EpochChallenge<N>,
        address: Address<N>,
        nonce: u64,
        minimum_proof_target: Option<u64>,
    ) -> Result<ProverSolution<N>> {
        // Retrieve the coinbase proving key.
        let pk = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        let polynomial = Self::prover_polynomial(epoch_challenge, address, nonce)?;

        let product_evaluations = {
            let polynomial_evaluations = pk.product_domain.in_order_fft_with_pc(&polynomial, &pk.fft_precomputation);
            let product_evaluations = pk.product_domain.mul_polynomials_in_evaluation_domain(
                polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evaluations().evaluations,
            );
            product_evaluations
        };
        let (commitment, _rand) = KZG10::commit_lagrange(&pk.lagrange_basis(), &product_evaluations, None, None)?;

        let partial_solution = PartialSolution::new(address, nonce, commitment);

        // Check that the minimum target is met.
        if let Some(minimum_target) = minimum_proof_target {
            let proof_target = partial_solution.to_target()?;
            ensure!(
                proof_target >= minimum_target,
                "Prover solution was below the necessary proof target ({proof_target} < {minimum_target})"
            );
        }

        let point = hash_commitment(&commitment)?;
        let product_eval_at_point = polynomial.evaluate(point) * epoch_challenge.epoch_polynomial().evaluate(point);

        let proof = KZG10::open_lagrange(
            &pk.lagrange_basis(),
            pk.product_domain_elements(),
            &product_evaluations,
            point,
            product_eval_at_point,
        )?;
        ensure!(!proof.is_hiding(), "The prover solution must contain a non-hiding proof");

        debug_assert!(KZG10::check(&pk.verifying_key, &commitment, point, product_eval_at_point, &proof)?);

        Ok(ProverSolution::new(partial_solution, proof))
    }

    /// Returns a coinbase solution for the given epoch challenge and prover solutions.
    ///
    /// # Note
    /// This method does *not* check that the prover solutions are valid.
    pub fn accumulate_unchecked(
        &self,
        epoch_challenge: &EpochChallenge<N>,
        prover_solutions: &[ProverSolution<N>],
    ) -> Result<CoinbaseSolution<N>> {
        // Ensure there exists prover solutions.
        if prover_solutions.is_empty() {
            bail!("Cannot accumulate an empty list of prover solutions.");
        }

        // Ensure the number of prover solutions does not exceed `MAX_PROVER_SOLUTIONS`.
        if prover_solutions.len() > N::MAX_PROVER_SOLUTIONS {
            bail!(
                "Cannot accumulate beyond {} prover solutions, found {}.",
                N::MAX_PROVER_SOLUTIONS,
                prover_solutions.len()
            );
        }

        // Retrieve the coinbase proving key.
        let pk = match self {
            Self::Prover(coinbase_proving_key) => coinbase_proving_key,
            Self::Verifier(_) => bail!("Cannot accumulate the coinbase puzzle with a verifier"),
        };
        ensure!(!has_duplicates(prover_solutions), "Cannot accumulate duplicate prover solutions");

        let (prover_polynomials, partial_solutions): (Vec<_>, Vec<_>) = cfg_iter!(prover_solutions)
            .filter_map(|solution| {
                if solution.proof().is_hiding() {
                    return None;
                }
                let polynomial = solution.to_prover_polynomial(epoch_challenge).ok()?;
                Some((polynomial, PartialSolution::new(solution.address(), solution.nonce(), solution.commitment())))
            })
            .unzip();

        // Compute the challenge points.
        let mut challenges = hash_commitments(partial_solutions.iter().map(|solution| *solution.commitment()))?;
        ensure!(challenges.len() == partial_solutions.len() + 1, "Invalid number of challenge points");

        // Pop the last challenge as the accumulator challenge point.
        let accumulator_point = match challenges.pop() {
            Some(point) => point,
            None => bail!("Missing the accumulator challenge point"),
        };

        // Accumulate the prover polynomial.
        let zero = DensePolynomial::zero;
        let accumulated_prover_polynomial = cfg_zip_fold!(
            cfg_into_iter!(prover_polynomials),
            challenges,
            zero,
            |mut accumulator, (mut prover_polynomial, challenge)| {
                prover_polynomial *= challenge;
                accumulator += &prover_polynomial;
                accumulator
            },
            DensePolynomial<_>
        );
        let product_eval_at_challenge_point = accumulated_prover_polynomial.evaluate(accumulator_point)
            * epoch_challenge.epoch_polynomial().evaluate(accumulator_point);

        // Compute the accumulator polynomial.
        let product_evals = {
            let accumulated_polynomial_evaluations =
                pk.product_domain.in_order_fft_with_pc(&accumulated_prover_polynomial.coeffs, &pk.fft_precomputation);
            pk.product_domain.mul_polynomials_in_evaluation_domain(
                accumulated_polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evaluations().evaluations,
            )
        };

        // Compute the coinbase proof.
        let proof = KZG10::open_lagrange(
            &pk.lagrange_basis(),
            pk.product_domain_elements(),
            &product_evals,
            accumulator_point,
            product_eval_at_challenge_point,
        )?;

        // Ensure the coinbase proof is non-hiding.
        if proof.is_hiding() {
            bail!("The coinbase proof must be non-hiding");
        }

        // Return the accumulated proof.
        Ok(CoinbaseSolution::new(partial_solutions, proof))
    }

    /// Returns `true` if the coinbase solution is valid.
    pub fn verify(
        &self,
        coinbase_solution: &CoinbaseSolution<N>,
        epoch_challenge: &EpochChallenge<N>,
        coinbase_target: u64,
        proof_target: u64,
    ) -> Result<bool> {
        // Ensure the coinbase solution is not empty.
        if coinbase_solution.is_empty() {
            bail!("The coinbase solution does not contain any partial solutions");
        }

        // Ensure the number of partial solutions does not exceed `MAX_PROVER_SOLUTIONS`.
        if coinbase_solution.len() > N::MAX_PROVER_SOLUTIONS {
            bail!(
                "The coinbase solution exceeds the allowed number of partial solutions. ({} > {})",
                coinbase_solution.len(),
                N::MAX_PROVER_SOLUTIONS
            );
        }

        // Ensure the coinbase proof is non-hiding.
        if coinbase_solution.proof().is_hiding() {
            bail!("The coinbase proof must be non-hiding");
        }

        // Ensure the coinbase proof meets the required coinbase target.
        if coinbase_solution.to_cumulative_proof_target()? < coinbase_target as u128 {
            bail!("The coinbase proof does not meet the coinbase target");
        }

        // Ensure the puzzle commitments are unique.
        if has_duplicates(coinbase_solution.puzzle_commitments()) {
            bail!("The coinbase solution contains duplicate puzzle commitments");
        }

        // Compute the prover polynomials.
        let prover_polynomials = cfg_iter!(coinbase_solution.partial_solutions())
            // Ensure that each of the prover solutions meets the required proof target.
            .map(|solution| match solution.to_target()? >= proof_target {
                // Compute the prover polynomial.
                true => solution.to_prover_polynomial(epoch_challenge),
                false => bail!("Prover puzzle does not meet the proof target requirements."),
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute the challenge points.
        let mut challenge_points =
            hash_commitments(coinbase_solution.partial_solutions().iter().map(|solution| *solution.commitment()))?;
        ensure!(
            challenge_points.len() == coinbase_solution.partial_solutions().len() + 1,
            "Invalid number of challenge points"
        );

        // Pop the last challenge point as the accumulator challenge point.
        let accumulator_point = match challenge_points.pop() {
            Some(point) => point,
            None => bail!("Missing the accumulator challenge point"),
        };

        // Compute the accumulator evaluation.
        let mut accumulator_evaluation = cfg_zip_fold!(
            cfg_iter!(prover_polynomials),
            &challenge_points,
            <N::PairingCurve as PairingEngine>::Fr::zero,
            |accumulator, (prover_polynomial, challenge_point)| {
                accumulator + (prover_polynomial.evaluate(accumulator_point) * challenge_point)
            },
            _
        );
        accumulator_evaluation *= &epoch_challenge.epoch_polynomial().evaluate(accumulator_point);

        // Compute the accumulator commitment.
        let commitments: Vec<_> =
            cfg_iter!(coinbase_solution.partial_solutions()).map(|solution| solution.commitment().0).collect();
        let fs_challenges = challenge_points.into_iter().map(|f| f.to_bigint()).collect::<Vec<_>>();
        let accumulator_commitment =
            KZGCommitment::<N::PairingCurve>(VariableBase::msm(&commitments, &fs_challenges).into());

        // Retrieve the coinbase verifying key.
        let coinbase_verifying_key = match self {
            Self::Prover(coinbase_proving_key) => &coinbase_proving_key.verifying_key,
            Self::Verifier(coinbase_verifying_key) => coinbase_verifying_key,
        };

        // Return the verification result.
        Ok(KZG10::check(
            coinbase_verifying_key,
            &accumulator_commitment,
            accumulator_point,
            accumulator_evaluation,
            coinbase_solution.proof(),
        )?)
    }

    /// Returns the coinbase proving key.
    pub fn coinbase_proving_key(&self) -> Result<&CoinbaseProvingKey<N>> {
        match self {
            Self::Prover(coinbase_proving_key) => Ok(coinbase_proving_key),
            Self::Verifier(_) => bail!("Cannot fetch the coinbase proving key with a verifier"),
        }
    }

    /// Returns the coinbase verifying key.
    pub fn coinbase_verifying_key(&self) -> &CoinbaseVerifyingKey<N> {
        match self {
            Self::Prover(coinbase_proving_key) => &coinbase_proving_key.verifying_key,
            Self::Verifier(coinbase_verifying_key) => coinbase_verifying_key,
        }
    }
}

impl<N: Network> CoinbasePuzzle<N> {
    /// Checks that the degree for the epoch and prover polynomial is within bounds,
    /// and returns the evaluation domain for the product polynomial.
    pub(crate) fn product_domain(degree: u32) -> Result<EvaluationDomain<N::Field>> {
        ensure!(degree != 0, "Degree cannot be zero");
        let num_coefficients = degree.checked_add(1).ok_or_else(|| anyhow!("Degree is too large"))?;
        let product_num_coefficients = num_coefficients
            .checked_mul(2)
            .and_then(|t| t.checked_sub(1))
            .ok_or_else(|| anyhow!("Degree is too large"))?;
        assert_eq!(product_num_coefficients, 2 * degree + 1);
        let product_domain =
            EvaluationDomain::new(product_num_coefficients.try_into()?).ok_or_else(|| anyhow!("Invalid degree"))?;
        assert_eq!(product_domain.size(), (product_num_coefficients as usize).checked_next_power_of_two().unwrap());
        Ok(product_domain)
    }

    /// Returns the prover polynomial for the coinbase puzzle.
    fn prover_polynomial(
        epoch_challenge: &EpochChallenge<N>,
        address: Address<N>,
        nonce: u64,
    ) -> Result<DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>> {
        let input = {
            let mut bytes = [0u8; 76];
            bytes[..4].copy_from_slice(&epoch_challenge.epoch_number().to_bytes_le()?);
            bytes[4..36].copy_from_slice(&epoch_challenge.epoch_block_hash().to_bytes_le()?);
            bytes[36..68].copy_from_slice(&address.to_bytes_le()?);
            bytes[68..].copy_from_slice(&nonce.to_le_bytes());
            bytes
        };
        Ok(hash_to_polynomial::<<N::PairingCurve as PairingEngine>::Fr>(&input, epoch_challenge.degree()))
    }
}
