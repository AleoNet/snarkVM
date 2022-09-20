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

mod data_structures;
pub use data_structures::*;

mod hash;
use hash::*;

#[cfg(test)]
mod tests;

use console::prelude::Network;
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain, Polynomial},
    msm::VariableBase,
    polycommit::kzg10::{self, Commitment, Randomness, UniversalParams as SRS, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::cfg_iter;

use rand::{CryptoRng, Rng};
use std::{collections::BTreeMap, marker::PhantomData, sync::atomic::AtomicBool};

pub struct CoinbasePuzzle<N: Network>(PhantomData<N>);

impl<N: Network> CoinbasePuzzle<N> {
    pub fn setup(config: PuzzleConfig, rng: &mut (impl CryptoRng + Rng)) -> SRS<N::PairingCurve> {
        // The SRS needs to be able to supporting commiting to the product of two degree `n`
        // polynomials.
        // This means the SRS that supports committing to a polynomial of degree `2n - 1`.
        KZG10::setup(2 * config.degree - 1, &kzg10::KZG10DegreeBoundsConfig::None, false, rng).unwrap()
    }

    pub fn trim(
        srs: &SRS<N::PairingCurve>,
        config: PuzzleConfig,
    ) -> (CoinbasePuzzleProvingKey<N>, CoinbasePuzzleVerifyingKey<N>) {
        // As above, we need to be able to commit to the product of two degree `n` polynomials.
        // This means the SRS that supports committing to a polynomial of degree `2n - 1`.
        let powers_of_beta_g = srs.powers_of_beta_g(0, 2 * config.degree - 1).unwrap().to_vec();
        let domain = EvaluationDomain::new(config.degree + 1).unwrap();
        let lagrange_basis_at_beta_g = srs.lagrange_basis(domain).unwrap();

        let vk = CoinbasePuzzleVerifyingKey::<N> {
            g: srs.power_of_beta_g(0).unwrap(),
            gamma_g: <N::PairingCurve as PairingEngine>::G1Affine::zero(), // We don't use gamma_g later on since we are not hiding.
            h: srs.h,
            beta_h: srs.beta_h,
            prepared_h: srs.prepared_h.clone(),
            prepared_beta_h: srs.prepared_beta_h.clone(),
        };
        let mut lagrange_basis_map = BTreeMap::new();
        lagrange_basis_map.insert(domain.size(), lagrange_basis_at_beta_g);

        let pk =
            CoinbasePuzzleProvingKey { powers_of_beta_g, lagrange_bases_at_beta_g: lagrange_basis_map, vk: vk.clone() };
        (pk, vk)
    }

    pub fn init_for_epoch(epoch_info: &EpochInfo, degree: usize) -> EpochChallenge<N> {
        let poly_input = &epoch_info.to_bytes_le();
        EpochChallenge { epoch_polynomial: hash_to_poly::<<N::PairingCurve as PairingEngine>::Fr>(poly_input, degree) }
    }

    fn sample_solution_polynomial(
        epoch_challenge: &EpochChallenge<N>,
        epoch_info: &EpochInfo,
        address: &PlaceholderAddress,
        nonce: u64,
    ) -> DensePolynomial<<N::PairingCurve as PairingEngine>::Fr> {
        let poly_input = {
            let mut bytes = [0u8; 48];
            bytes[..8].copy_from_slice(&epoch_info.to_bytes_le());
            bytes[8..40].copy_from_slice(&address.to_bytes_le());
            bytes[40..].copy_from_slice(&nonce.to_le_bytes());
            bytes
        };
        hash_to_poly::<<N::PairingCurve as PairingEngine>::Fr>(&poly_input, epoch_challenge.degree())
    }

    pub fn prove(
        pk: &CoinbasePuzzleProvingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
        address: &PlaceholderAddress,
        nonce: u64,
    ) -> ProverPuzzleSolution<N> {
        let polynomial = Self::sample_solution_polynomial(epoch_challenge, epoch_info, address, nonce);

        let product = Polynomial::from(&polynomial * &epoch_challenge.epoch_polynomial);
        let (commitment, _rand) = KZG10::commit(&pk.powers(), &product, None, &AtomicBool::default(), None).unwrap();
        let point = hash_commitment(&commitment);
        let proof = KZG10::open(&pk.powers(), product.as_dense().unwrap(), point, &_rand).unwrap();
        assert!(!proof.is_hiding());

        #[cfg(debug_assertions)]
        {
            let product_eval = product.evaluate(point);
            assert!(KZG10::check(&pk.vk, &commitment, point, product_eval, &proof).unwrap());
        }

        ProverPuzzleSolution { address: *address, nonce, commitment, proof }
    }

    pub fn accumulate(
        pk: &CoinbasePuzzleProvingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
        prover_solutions: &[ProverPuzzleSolution<N>],
    ) -> CombinedPuzzleSolution<N> {
        let (polynomials, partial_solutions): (Vec<_>, Vec<_>) = cfg_iter!(prover_solutions)
            .filter_map(|solution| {
                if solution.proof.is_hiding() {
                    return None;
                }
                // TODO: check difficulty of solution
                let polynomial =
                    Self::sample_solution_polynomial(epoch_challenge, epoch_info, &solution.address, solution.nonce);
                let point = hash_commitment(&solution.commitment);
                let epoch_challenge_eval = epoch_challenge.epoch_polynomial.evaluate(point);
                let polynomial_eval = polynomial.evaluate(point);
                let product_eval = epoch_challenge_eval * polynomial_eval;
                let check_result =
                    KZG10::check(&pk.vk, &solution.commitment, point, product_eval, &solution.proof).ok();
                if let Some(true) = check_result {
                    Some((polynomial, (solution.address, solution.nonce, solution.commitment)))
                } else {
                    None
                }
            })
            .unzip();

        let mut fs_challenges = hash_commitments(partial_solutions.iter().map(|(_, _, c)| *c));
        let point = fs_challenges.pop().unwrap();

        let combined_polynomial = cfg_iter!(polynomials)
            .zip(fs_challenges)
            .fold(DensePolynomial::zero, |acc, (poly, challenge)| &acc + &(poly * challenge))
            .sum();
        let combined_product = &combined_polynomial * &epoch_challenge.epoch_polynomial;
        let proof = KZG10::open(&pk.powers(), &combined_product, point, &Randomness::empty()).unwrap();
        CombinedPuzzleSolution { individual_puzzle_solutions: partial_solutions, proof }
    }

    pub fn verify(
        vk: &CoinbasePuzzleVerifyingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
        combined_solution: &CombinedPuzzleSolution<N>,
    ) -> bool {
        if combined_solution.individual_puzzle_solutions.is_empty() {
            return false;
        }
        if combined_solution.proof.is_hiding() {
            return false;
        }
        let polynomials: Vec<_> = cfg_iter!(combined_solution.individual_puzzle_solutions)
            .map(|(address, nonce, _)| {
                // TODO: check difficulty of solution
                Self::sample_solution_polynomial(epoch_challenge, epoch_info, address, *nonce)
            })
            .collect();

        // Compute challenges
        let mut fs_challenges =
            hash_commitments(combined_solution.individual_puzzle_solutions.iter().map(|(_, _, c)| *c));
        let point = fs_challenges.pop().unwrap();

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
            cfg_iter!(combined_solution.individual_puzzle_solutions).map(|(_, _, c)| c.0).collect();
        let fs_challenges = fs_challenges.into_iter().map(|f| f.to_repr()).collect::<Vec<_>>();
        let combined_commitment = VariableBase::msm(&commitments, &fs_challenges);
        let combined_commitment: Commitment<N::PairingCurve> = Commitment(combined_commitment.into());
        KZG10::check(vk, &combined_commitment, point, combined_eval, &combined_solution.proof).unwrap()
    }
}
