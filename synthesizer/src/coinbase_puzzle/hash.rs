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

use console::prelude::{bail, cfg_into_iter, ensure, Result, Zero};
use snarkvm_algorithms::{fft::DensePolynomial, polycommit::kzg10::KZGCommitment};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::CanonicalSerialize;

use blake2::Digest;
use blake2b_simd::Params as blake2b;
use blake2s_simd::Params as blake2s;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub fn hash_to_coefficients<F: PrimeField>(input: &[u8], num_coefficients: u32) -> Vec<F> {
    // Hash the input.
    let hash = blake2s::new().hash_length(32).to_state().update(&input).finalize();
    // Hash with a counter and return the coefficients.
    cfg_into_iter!(0..num_coefficients)
        .map(|counter| {
            let mut input_with_counter = [0u8; 36];
            input_with_counter[..32].copy_from_slice(&hash.as_bytes());
            input_with_counter[32..].copy_from_slice(&counter.to_le_bytes());
            let input_hash = blake2b::new().hash_length(64).hash(&input_with_counter);
            F::from_bytes_le_mod_order(input_hash.as_bytes())
        })
        .collect()
}

pub fn hash_to_polynomial<F: PrimeField>(input: &[u8], degree: u32) -> DensePolynomial<F> {
    // Hash the input into coefficients.
    let coefficients = hash_to_coefficients(input, degree + 1);
    // Construct the polynomial from the coefficients.
    DensePolynomial::from_coefficients_vec(coefficients)
}

pub fn hash_commitment<E: PairingEngine>(commitment: &KZGCommitment<E>) -> Result<E::Fr> {
    // Convert the commitment into bytes.
    let mut bytes = Vec::with_capacity(96);
    commitment.serialize_uncompressed(&mut bytes)?;
    ensure!(bytes.len() == 96, "Invalid commitment byte length for hashing");

    // Return the hash of the commitment.
    let result = blake2b::new().hash_length(64).hash(&bytes);
    let input_hash = result.as_bytes();
    Ok(E::Fr::from_bytes_le_mod_order(input_hash))
}

pub fn hash_commitments<E: PairingEngine>(
    commitments: impl ExactSizeIterator<Item = KZGCommitment<E>>,
) -> Result<Vec<E::Fr>> {
    // Retrieve the number of commitments.
    let num_commitments = match u32::try_from(commitments.len()) {
        Ok(num_commitments) => num_commitments,
        Err(_) => bail!("Cannot hash more than 2^32 commitments: found {}", commitments.len()),
    };
    ensure!(!num_commitments.is_zero(), "No commitments provided for hashing");

    // Convert the commitments into bytes.
    let bytes = commitments
        .flat_map(|commitment| {
            let mut bytes = Vec::with_capacity(96);
            commitment.serialize_uncompressed(&mut bytes).unwrap();
            bytes
        })
        .collect::<Vec<_>>();
    ensure!(bytes.len() == 96 * usize::try_from(num_commitments)?, "Invalid commitment byte length for hashing");

    // Hash the commitment bytes into coefficients.
    Ok(hash_to_coefficients(&bytes, num_commitments + 1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CoinbasePuzzle, EpochChallenge, PartialSolution, ProverSolution, PuzzleConfig};
    use console::{
        account::{Address, PrivateKey},
        network::Network,
        prelude::{TestRng, Uniform},
    };
    use snarkvm_algorithms::polycommit::kzg10::KZG10;
    use snarkvm_curves::bls12_377::Fr;

    use rand::RngCore;
    use std::time::Duration;

    type CurrentNetwork = console::network::Testnet3;

    /// Computes the hash to coefficients without `blake2*_simd`.
    pub fn hash_to_coefficients_no_simd<F: PrimeField>(input: &[u8], num_coefficients: u32) -> Vec<F> {
        // Hash the input.
        let hash = blake2::Blake2s256::digest(input);
        // Hash with a counter and return the coefficients.
        cfg_into_iter!(0..num_coefficients)
            .map(|counter| {
                let mut input_with_counter = [0u8; 36];
                input_with_counter[..32].copy_from_slice(&hash);
                input_with_counter[32..].copy_from_slice(&counter.to_le_bytes());
                F::from_bytes_le_mod_order(&blake2::Blake2b512::digest(input_with_counter))
            })
            .collect()
    }

    /// Computes the hash of the commitment without `blake2*_simd`.
    pub fn hash_commitment<E: PairingEngine>(commitment: &KZGCommitment<E>) -> Result<E::Fr> {
        // Convert the commitment into bytes.
        let mut bytes = Vec::with_capacity(96);
        commitment.serialize_uncompressed(&mut bytes)?;
        ensure!(bytes.len() == 96, "Invalid commitment byte length for hashing");

        // Return the hash of the commitment.
        Ok(E::Fr::from_bytes_le_mod_order(&blake2::Blake2b512::digest(&bytes)))
    }

    /// Compute the proof without `blake2*_simd`.
    pub fn prove_no_simd<N: Network>(
        puzzle: &CoinbasePuzzle<N>,
        epoch_challenge: &EpochChallenge<N>,
        address: Address<N>,
        nonce: u64,
    ) -> Result<ProverSolution<N>> {
        // Retrieve the coinbase proving key.
        let pk = match puzzle {
            CoinbasePuzzle::Prover(coinbase_proving_key) => coinbase_proving_key,
            CoinbasePuzzle::Verifier(_) => bail!("Cannot prove the coinbase puzzle with a verifier"),
        };

        let polynomial = CoinbasePuzzle::prover_polynomial(epoch_challenge, address, nonce)?;

        let product_evaluations = {
            let polynomial_evaluations = pk.product_domain.in_order_fft_with_pc(&polynomial, &pk.fft_precomputation);
            let product_evaluations = pk.product_domain.mul_polynomials_in_evaluation_domain(
                &polynomial_evaluations,
                &epoch_challenge.epoch_polynomial_evaluations().evaluations,
            );
            product_evaluations
        };
        let (commitment, _rand) =
            KZG10::commit_lagrange(&pk.lagrange_basis(), &product_evaluations, None, &Default::default(), None)?;
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

        Ok(ProverSolution::new(PartialSolution::new(address, nonce, commitment), proof))
    }

    #[test]
    fn test_hash_to_coefficients() {
        let input = b"test";
        let coefficients = hash_to_coefficients::<Fr>(input, 10);
        assert_eq!(coefficients.len(), 10);
    }

    #[test]
    fn test_hash_to_coefficients_simd() {
        for num_coefficients in (1..10000).step_by(101) {
            for num_bytes in (1..1000).step_by(101) {
                // Prepare the time loggers.
                let mut time_a = Duration::new(0, 0);
                let mut time_b = Duration::new(0, 0);

                for _ in 0..100 {
                    // Sample a different random input between iterations.
                    let input = (0..num_bytes).map(|_| rand::random::<u8>()).collect::<Vec<_>>();

                    // Compute the coefficients using the `blake2*_simd` crate.
                    let time = std::time::Instant::now();
                    let coefficients = hash_to_coefficients::<Fr>(&input, num_coefficients);
                    time_a += time.elapsed();

                    // Compute the coefficients without using the `blake2*_simd` crate.
                    let time = std::time::Instant::now();
                    let coefficients_no_simd = hash_to_coefficients_no_simd::<Fr>(&input, num_coefficients);
                    time_b += time.elapsed();

                    // Ensure the coefficients are the same.
                    assert_eq!(coefficients, coefficients_no_simd);
                }

                // Log the time taken.
                println!("{num_coefficients} {num_bytes} {}", time_a.as_nanos() as f64 / time_b.as_nanos() as f64);
            }
        }
    }

    #[test]
    fn test_prove_simd() {
        let mut rng = TestRng::default();

        let max_degree = 1 << 14;
        let max_config = PuzzleConfig { degree: max_degree };
        let srs = CoinbasePuzzle::<CurrentNetwork>::setup(max_config).unwrap();

        let degree = (1 << 13) - 1;
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzle::<CurrentNetwork>::trim(&srs, config).unwrap();
        let epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();

        for batch_size in (1..10).step_by(2) {
            // Prepare the time loggers.
            let mut time_a = Duration::new(0, 0);
            let mut time_b = Duration::new(0, 0);

            for _ in 0..100 {
                let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng).unwrap();
                let address = Address::try_from(private_key).unwrap();
                let nonce = u64::rand(&mut rng);

                // Compute the solutions using the `blake2*_simd` crate.
                let time = std::time::Instant::now();
                let solutions = (0..batch_size)
                    .map(|_| puzzle.prove(&epoch_challenge, address, nonce).unwrap())
                    .collect::<Vec<_>>();
                time_a += time.elapsed();

                // Compute the coefficients without using the `blake2*_simd` crate.
                let time = std::time::Instant::now();
                let solutions_no_simd = (0..batch_size)
                    .map(|_| prove_no_simd(&puzzle, &epoch_challenge, address, nonce).unwrap())
                    .collect::<Vec<_>>();
                time_b += time.elapsed();

                // Ensure the solutions are the same.
                assert_eq!(solutions, solutions_no_simd);
            }

            // Log the time taken.
            println!("{batch_size} {}", time_a.as_nanos() as f64 / time_b.as_nanos() as f64);
        }
    }
}
