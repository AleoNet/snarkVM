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

use std::{marker::PhantomData, sync::atomic::AtomicBool};

use snarkvm_curves::PairingEngine;
use snarkvm_fields::{PrimeField, Zero};

mod data_structures;
pub use data_structures::*;

mod hash;
use hash::*;
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use snarkvm_utilities::cfg_iter;

use crate::{
    fft::{DensePolynomial, Polynomial},
    msm::VariableBase,
    polycommit::kzg10::{Commitment, Randomness, KZG10},
};

pub struct CoinbasePuzzle<E: PairingEngine>(PhantomData<E>);

impl<E: PairingEngine> CoinbasePuzzle<E> {
    pub fn setup() -> SRS<E> {
        todo!()
    }

    pub fn trim(_degree: usize) -> (ProvingKey<E>, VerifyingKey<E>) {
        todo!()
    }

    pub fn init_for_epoch() -> EpochChallenge<E> {
        todo!()
    }

    fn sample_solution_polynomial(
        epoch_challenge: &EpochChallenge<E>,
        epoch_info: &EpochInfo,
        address: &Address,
        nonce: u64,
    ) -> DensePolynomial<E::Fr> {
        let poly_input = {
            let mut bytes = [0u8; 48];
            bytes[..8].copy_from_slice(&epoch_info.to_bytes_le());
            bytes[8..40].copy_from_slice(&address.to_bytes_le());
            bytes[40..].copy_from_slice(&nonce.to_le_bytes());
            bytes
        };
        hash_to_poly::<E::Fr>(&poly_input, epoch_challenge.degree())
    }

    pub fn prove(
        pk: &ProvingKey<E>,
        epoch_challenge: &EpochChallenge<E>,
        epoch_info: &EpochInfo,
        address: &Address,
        nonce: u64,
    ) -> ProverPuzzleSolution<E> {
        let polynomial = Self::sample_solution_polynomial(epoch_challenge, epoch_info, address, nonce);

        let product = Polynomial::from(&polynomial * &epoch_challenge.epoch_polynomial);
        let (commitment, _rand) = KZG10::commit(&pk.ck.powers(), &product, None, &AtomicBool::default(), None).unwrap();
        let point = hash_commitment(&commitment);
        let proof = KZG10::open(&pk.ck.powers(), product.as_dense().unwrap(), point, &_rand).unwrap();
        ProverPuzzleSolution { address: *address, nonce, commitment, proof }
    }

    pub fn accumulate(
        pk: &ProvingKey<E>,
        epoch_challenge: &EpochChallenge<E>,
        epoch_info: &EpochInfo,
        prover_solutions: &[ProverPuzzleSolution<E>],
    ) -> CombinedPuzzleSolution<E> {
        let (polynomials, partial_solutions): (Vec<_>, Vec<_>) = cfg_iter!(prover_solutions)
            .filter_map(|solution| {
                // TODO: check difficulty of solution
                let polynomial =
                    Self::sample_solution_polynomial(epoch_challenge, epoch_info, &solution.address, solution.nonce);
                let point = hash_commitment(&solution.commitment);
                let epoch_challenge_eval = epoch_challenge.epoch_polynomial.evaluate(point);
                let polynomial_eval = polynomial.evaluate(point);
                let product_eval = epoch_challenge_eval * polynomial_eval;
                let check_result =
                    KZG10::check(&pk.vk.vk, &solution.commitment, point, product_eval, &solution.proof).ok();
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
        let proof = KZG10::open(&pk.ck.powers(), &combined_product, point, &Randomness::empty()).unwrap();
        CombinedPuzzleSolution { individual_puzzle_solutions: partial_solutions, proof }
    }

    pub fn verify(
        vk: &VerifyingKey<E>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<E>,
        combined_solution: &CombinedPuzzleSolution<E>,
    ) -> bool {
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
            .fold(E::Fr::zero, |acc, (poly, challenge)| acc + (poly.evaluate(point) * challenge))
            .sum();
        combined_eval *= &epoch_challenge.epoch_polynomial.evaluate(point);

        // Compute combined commitment
        let commitments: Vec<_> =
            cfg_iter!(combined_solution.individual_puzzle_solutions).map(|(_, _, c)| c.0).collect();
        let fs_challenges = fs_challenges.into_iter().map(|f| f.to_repr()).collect::<Vec<_>>();
        let combined_commitment = VariableBase::msm(&commitments, &fs_challenges);
        let combined_commitment: Commitment<E> = Commitment(combined_commitment.into());
        KZG10::check(&vk.vk, &combined_commitment, point, combined_eval, &combined_solution.proof).unwrap()
    }
}
