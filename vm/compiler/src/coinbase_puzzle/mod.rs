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

#[cfg(feature = "parallel")]
use rayon::prelude::*;

mod helpers;
pub use helpers::*;

mod hash;
use hash::*;

#[cfg(test)]
mod tests;

use crate::{UniversalSRS, MAX_NUM_PROOFS};
use console::{
    account::Address,
    prelude::{anyhow, bail, cfg_iter, ensure, Network, Result, ToBytes},
    program::cfg_into_iter,
};
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    polycommit::kzg10::{UniversalParams as SRS, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::Zero;

#[cfg(any(test, feature = "setup"))]
use console::prelude::{CryptoRng, Rng};
#[cfg(any(test, feature = "setup"))]
use snarkvm_algorithms::polycommit::kzg10;

use std::{marker::PhantomData, sync::atomic::AtomicBool};

pub struct CoinbasePuzzle<N: Network>(PhantomData<N>);

impl<N: Network> CoinbasePuzzle<N> {
    /// Initializes a new `SRS` for the coinbase puzzle.
    #[cfg(any(test, feature = "setup"))]
    pub fn setup<R: Rng + CryptoRng>(config: PuzzleConfig, rng: &mut R) -> Result<SRS<N::PairingCurve>> {
        // The SRS must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        Ok(KZG10::setup((2 * config.degree - 1).try_into()?, &kzg10::KZGDegreeBounds::None, false, rng)?)
    }

    /// Load the coinbase puzzle proving and verifying keys.
    pub fn load(max_degree: u32) -> Result<(CoinbaseProvingKey<N>, CoinbaseVerifyingKey<N>)> {
        // Load the universal SRS.
        let universal_srs = UniversalSRS::<N>::load()?;
        // Trim the universal SRS to the maximum degree.
        Self::trim(&*universal_srs, PuzzleConfig { degree: max_degree })
    }

    pub fn trim(
        srs: &SRS<N::PairingCurve>,
        config: PuzzleConfig,
    ) -> Result<(CoinbaseProvingKey<N>, CoinbaseVerifyingKey<N>)> {
        // As above, we must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        // Since the upper bound to `srs.powers_of_beta_g` takes as input the number
        // of coefficients. The degree of the product has `2n - 1` coefficients.
        //
        // Hence, we request the powers of beta for the interval [0, 2n].
        let num_coefficients = config.degree + 1;
        let product_num_coefficients = 2 * num_coefficients - 1;
        let powers_of_beta_g = srs.powers_of_beta_g(0, product_num_coefficients.try_into()?)?.to_vec();
        let product_domain =
            EvaluationDomain::new((2 * config.degree - 1).try_into()?).ok_or_else(|| anyhow!("Invalid degree"))?;
        let lagrange_basis_at_beta_g = srs.lagrange_basis(product_domain)?;
        let fft_precomputation = product_domain.precompute_fft();
        let product_domain_elements = product_domain.elements().collect();

        let vk = CoinbaseVerifyingKey::<N> {
            g: srs.power_of_beta_g(0)?,
            gamma_g: <N::PairingCurve as PairingEngine>::G1Affine::zero(), // We don't use gamma_g later on since we are not hiding.
            h: srs.h,
            beta_h: srs.beta_h,
            prepared_h: srs.prepared_h.clone(),
            prepared_beta_h: srs.prepared_beta_h.clone(),
        };

        let pk = CoinbaseProvingKey {
            powers_of_beta_g,
            product_domain,
            product_domain_elements,
            lagrange_basis_at_beta_g,
            fft_precomputation,
            verifying_key: vk.clone(),
        };
        Ok((pk, vk))
    }

    // TODO (raychu86): Create a "candidate_prove", just output the commitment -> then finalize the prove.
    /// Returns a prover solution to the coinbase puzzle.
    pub fn prove(
        pk: &CoinbaseProvingKey<N>,
        epoch_challenge: &EpochChallenge<N>,
        address: &Address<N>,
        nonce: u64,
    ) -> Result<ProverSolution<N>> {
        let polynomial = Self::prover_polynomial(epoch_challenge, address, nonce)?;

        let product_evaluations = {
            let polynomial_evaluations = pk.product_domain.in_order_fft_with_pc(&polynomial, &pk.fft_precomputation);
            let product_evaluations = pk.product_domain.mul_polynomials_in_evaluation_domain(
                &polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evaluations().evaluations,
            );
            product_evaluations
        };
        let (commitment, _rand) =
            KZG10::commit_lagrange(&pk.lagrange_basis(), &product_evaluations, None, &AtomicBool::default(), None)?;
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

        Ok(ProverSolution::new(PartialSolution::new(*address, nonce, commitment), proof))
    }

    /// Returns a coinbase solution for the given epoch challenge and prover solutions.
    ///
    /// # Note
    /// This method does *not* check that the prover solutions are valid.
    pub fn accumulate(
        pk: &CoinbaseProvingKey<N>,
        epoch_challenge: &EpochChallenge<N>,
        prover_solutions: &[ProverSolution<N>],
    ) -> Result<CoinbaseSolution<N>> {
        // Ensure there exists prover solutions.
        if prover_solutions.is_empty() {
            bail!("Cannot accumulate an empty list of prover solutions.");
        }

        // Ensure the number of prover solutions does not exceed `MAX_NUM_PROOFS`.
        if prover_solutions.len() > MAX_NUM_PROOFS {
            bail!("Cannot accumulate beyond {MAX_NUM_PROOFS} prover solutions, found {}.", prover_solutions.len());
        }

        let (prover_polynomials, partial_solutions): (Vec<_>, Vec<_>) = cfg_iter!(prover_solutions)
            .filter_map(|solution| {
                if solution.proof().is_hiding() {
                    return None;
                }
                let polynomial = solution.to_prover_polynomial(epoch_challenge).unwrap();
                Some((polynomial, PartialSolution::new(*solution.address(), solution.nonce(), *solution.commitment())))
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

        // Construct the provers polynomial.
        let accumulated_prover_polynomial = cfg_into_iter!(prover_polynomials)
            .zip(challenges)
            .fold(DensePolynomial::zero, |mut accumulator, (mut prover_polynomial, challenge)| {
                prover_polynomial *= challenge;
                accumulator += &prover_polynomial;
                accumulator
            })
            .sum::<DensePolynomial<_>>();
        let product_eval_at_challenge_point = accumulated_prover_polynomial.evaluate(accumulator_point)
            * epoch_challenge.epoch_polynomial().evaluate(accumulator_point);

        // Compute the accumulator polynomial.
        let product_evals = {
            let accumulated_polynomial_evaluations =
                pk.product_domain.in_order_fft_with_pc(&accumulated_prover_polynomial.coeffs, &pk.fft_precomputation);
            pk.product_domain.mul_polynomials_in_evaluation_domain(
                &accumulated_polynomial_evaluations,
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
}

impl<N: Network> CoinbasePuzzle<N> {
    /// Returns the prover polynomial for the coinbase puzzle.
    fn prover_polynomial(
        epoch_challenge: &EpochChallenge<N>,
        address: &Address<N>,
        nonce: u64,
    ) -> Result<DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>> {
        let input = {
            let mut bytes = [0u8; 80];
            bytes[..40].copy_from_slice(&epoch_challenge.to_bytes_le()?);
            bytes[40..72].copy_from_slice(&address.to_bytes_le()?);
            bytes[72..].copy_from_slice(&nonce.to_le_bytes());
            bytes
        };
        hash_to_polynomial::<<N::PairingCurve as PairingEngine>::Fr>(&input, epoch_challenge.degree()?)
    }
}
