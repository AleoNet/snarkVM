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

use console::prelude::{bail, cfg_into_iter, ensure, Result, Zero};
use snarkvm_algorithms::{fft::DensePolynomial, polycommit::kzg10::KZGCommitment};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::CanonicalSerialize;

use blake2::Digest;

#[cfg(not(feature = "serial"))]
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
            F::from_bytes_le_mod_order(&blake2::Blake2b512::digest(input_with_counter))
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
    Ok(E::Fr::from_bytes_le_mod_order(&blake2::Blake2b512::digest(&bytes)))
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
