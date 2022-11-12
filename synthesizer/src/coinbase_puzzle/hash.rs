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
use blake2b_simd::Params;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub fn hash_to_coefficients<F: PrimeField>(input: &[u8], num_coefficients: u32) -> Vec<F> {
    // Hash the input.
    let hash = blake2::Blake2s256::digest(input);
    // Hash with a counter and return the coefficients.
    cfg_into_iter!(0..num_coefficients)
        .map(|counter| {
            let mut input_with_counter = [0u8; 36];
            input_with_counter[..32].copy_from_slice(&hash);
            input_with_counter[32..].copy_from_slice(&counter.to_le_bytes());
            let input_hash = Params::new().hash_length(64).hash(&input_with_counter);
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
    let result = Params::new().hash_length(64).hash(&bytes);
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
    use snarkvm_curves::bls12_377::Fr;
    use std::time::Duration;

    /// Computes the hash to coefficients without `blake2b_simd`.
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

    #[test]
    fn test_hash_to_coefficients() {
        let input = b"test";
        let coefficients = hash_to_coefficients::<Fr>(input, 10);
        assert_eq!(coefficients.len(), 10);
    }

    #[test]
    fn test_hash_to_coefficients_blake2b() {
        for i in (1..1000).step_by(80) {
            // Sample a random input.
            let input = (0..i).map(|_| rand::random::<u8>()).collect::<Vec<_>>();

            for j in (1..10000).step_by(101) {
                // Prepare the time loggers.
                let mut time_a = Duration::new(0, 0);
                let mut time_b = Duration::new(0, 0);

                for _ in 0..10 {
                    // Compute the coefficients using the `blake2b_simd` crate.
                    let time = std::time::Instant::now();
                    let coefficients = hash_to_coefficients::<Fr>(&input, j);
                    time_a += time.elapsed();

                    // Compute the coefficients without using the `blake2b_simd` crate.
                    let time = std::time::Instant::now();
                    let coefficients_no_simd = hash_to_coefficients_no_simd::<Fr>(&input, j);
                    time_b += time.elapsed();

                    // Ensure the coefficients are the same.
                    assert_eq!(coefficients, coefficients_no_simd);
                }

                // Log the time taken.
                println!("{i} {j} {}", time_a.as_nanos() as f64 / time_b.as_nanos() as f64);
            }
        }
    }
}
