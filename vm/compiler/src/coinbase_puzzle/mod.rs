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

use crate::UniversalSRS;
use console::{
    account::Address,
    prelude::{anyhow, bail, cfg_iter, ensure, CryptoRng, Network, Result, Rng, ToBytes},
    program::cfg_into_iter,
};
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    polycommit::kzg10::{self, KZGRandomness, UniversalParams as SRS, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::Zero;

use std::{collections::BTreeMap, marker::PhantomData, sync::atomic::AtomicBool};

pub struct CoinbasePuzzle<N: Network>(PhantomData<N>);

impl<N: Network> CoinbasePuzzle<N> {
    /// Initializes a new `SRS` for the coinbase puzzle.
    pub fn setup<R: Rng + CryptoRng>(config: PuzzleConfig, rng: &mut R) -> Result<SRS<N::PairingCurve>> {
        // The SRS must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        Ok(KZG10::setup((2 * config.degree - 1).try_into()?, &kzg10::KZGDegreeBounds::None, false, rng)?)
    }

    pub fn trim(
        srs: &SRS<N::PairingCurve>,
        config: PuzzleConfig,
    ) -> Result<(CoinbaseProvingKey<N>, CoinbaseVerifyingKey<N>)> {
        // As above, we must support committing to the product of two degree `n` polynomials.
        // Thus, the SRS must support committing to a polynomial of degree `2n - 1`.
        let powers_of_beta_g = srs.powers_of_beta_g(0, (2 * config.degree - 1).try_into()?)?.to_vec();
        let product_domain =
            EvaluationDomain::new((2 * config.degree - 1).try_into()?).ok_or_else(|| anyhow!("Invalid degree"))?;
        let lagrange_basis_at_beta_g = srs.lagrange_basis(product_domain)?;
        let fft_precomputation = product_domain.precompute_fft();

        let vk = CoinbaseVerifyingKey::<N> {
            g: srs.power_of_beta_g(0)?,
            gamma_g: <N::PairingCurve as PairingEngine>::G1Affine::zero(), // We don't use gamma_g later on since we are not hiding.
            h: srs.h,
            beta_h: srs.beta_h,
            prepared_h: srs.prepared_h.clone(),
            prepared_beta_h: srs.prepared_beta_h.clone(),
        };
        let mut lagrange_basis_map = BTreeMap::new();
        lagrange_basis_map.insert(product_domain.size(), lagrange_basis_at_beta_g);

        let pk = CoinbaseProvingKey {
            product_domain,
            powers_of_beta_g,
            lagrange_bases_at_beta_g: lagrange_basis_map,
            fft_precomputation,
            verifying_key: vk.clone(),
        };
        Ok((pk, vk))
    }

    /// Load the coinbase puzzle proving and verifying keys.
    pub fn load(max_degree: u32) -> Result<(CoinbaseProvingKey<N>, CoinbaseVerifyingKey<N>)> {
        // Load the universal SRS.
        let universal_srs = UniversalSRS::<N>::load()?;

        let max_config = PuzzleConfig { degree: max_degree };

        Self::trim(&*universal_srs, max_config)
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

        let product = {
            let polynomial_evaluations = pk.product_domain.in_order_fft_with_pc(&polynomial, &pk.fft_precomputation);
            let product_evals = pk.product_domain.mul_polynomials_in_evaluation_domain(
                &polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evals.evaluations,
            );
            DensePolynomial::from_coefficients_vec(pk.product_domain.ifft(&product_evals)).into()
        };
        let (commitment, _rand) = KZG10::commit(&pk.powers(), &product, None, &AtomicBool::default(), None)?;
        let point = hash_commitment(&commitment)?;
        let proof = KZG10::open(&pk.powers(), product.as_dense().unwrap(), point, &_rand)?;
        assert!(!proof.is_hiding());

        #[cfg(debug_assertions)]
        {
            let product_eval = product.evaluate(point);
            assert!(KZG10::check(&pk.verifying_key, &commitment, point, product_eval, &proof)?);
        }

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

        // Compute the accumulator polynomial.
        let product_polynomial = {
            let accumulated_polynomial_evaluations =
                pk.product_domain.in_order_fft_with_pc(&accumulated_prover_polynomial.coeffs, &pk.fft_precomputation);
            let product_evals = pk.product_domain.mul_polynomials_in_evaluation_domain(
                &accumulated_polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evals.evaluations,
            );
            DensePolynomial::from_coefficients_vec(pk.product_domain.ifft(&product_evals))
        };

        // Compute the accumulator proof.
        let proof = KZG10::open(&pk.powers(), &product_polynomial, accumulator_point, &KZGRandomness::empty())?;

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
            let mut bytes = [0u8; 84];
            bytes[..44].copy_from_slice(&epoch_challenge.to_bytes_le()?);
            bytes[44..76].copy_from_slice(&address.to_bytes_le()?);
            bytes[76..].copy_from_slice(&nonce.to_le_bytes());
            bytes
        };
        hash_to_polynomial::<<N::PairingCurve as PairingEngine>::Fr>(&input, epoch_challenge.degree()?)
    }
}
