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

use console::{prelude::{bail, cfg_into_iter, ensure, Result, Zero, FromBits}, program::Network, types::Field};
use snarkvm_algorithms::{fft::DensePolynomial, polycommit::kzg10::KZGCommitment};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{CanonicalSerialize, ToBits};


use blake2::Digest;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub fn hash_to_coefficients<N: Network>(input: &[u8], num_coefficients: u32) -> Result<Vec<N::Field>> {
    const CHUNK_SIZE: u32 = 2;
    let fields =
        input.to_bits_le().chunks(N::Field::size_in_data_bits()).map(Field::from_bits_le).collect::<Result<Vec<_>>>()?;
    if num_coefficients < 1000 || (num_coefficients % CHUNK_SIZE != 0) {
        Ok(N::hash_many_psd8(&fields, num_coefficients as u16).into_iter().map(|s| *s).collect::<Vec<_>>())
    } else {
        // Pack the bits into field elements.
        let input_hash = N::hash_psd8(&fields)?;
        let coefficients_per_chunk = num_coefficients / CHUNK_SIZE;
        let result = cfg_into_iter!(0..CHUNK_SIZE).flat_map(|i| {
            let hash_input = [input_hash, Field::from_u32(i as u32)];
            N::hash_many_psd8(&hash_input, coefficients_per_chunk as u16).into_iter().map(|s| *s).collect::<Vec<_>>()
        }).collect::<Vec<N::Field>>();
        ensure!(result.len() == num_coefficients as usize, "Did not hash enough coefficients");
        Ok(result)

    }
        // Ok(.into_iter().map(|s| *s).collect::<Vec<N::Field>>())
    // cfg_into_iter!(0..num_coefficients).map(|i| {
    // }).collect()
}

pub fn hash_to_polynomial<N: Network>(input: &[u8], degree: u32) -> Result<DensePolynomial<N::Field>> {
    // Hash the input into coefficients.
    let coefficients = hash_to_coefficients::<N>(input, degree + 1)?;
    // Construct the polynomial from the coefficients.
    Ok(DensePolynomial::from_coefficients_vec(coefficients))
}

pub fn hash_commitment<E: PairingEngine>(commitment: &KZGCommitment<E>) -> Result<E::Fr> {
    // Convert the commitment into bytes.
    let mut bytes = Vec::with_capacity(96);
    commitment.serialize_uncompressed(&mut bytes)?;
    ensure!(bytes.len() == 96, "Invalid commitment byte length for hashing");

    // Return the hash of the commitment.
    Ok(E::Fr::from_bytes_le_mod_order(&blake2::Blake2b512::digest(&bytes)))
}

pub fn hash_commitments<N: Network>(
    commitments: impl ExactSizeIterator<Item = KZGCommitment<N::PairingCurve>>,
) -> Result<Vec<N::Field>> {
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
    hash_to_coefficients::<N>(&bytes, num_commitments + 1)
}
