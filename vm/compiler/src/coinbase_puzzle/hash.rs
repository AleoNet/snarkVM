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

use snarkvm_algorithms::{fft::DensePolynomial, polycommit::kzg10::Commitment};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_into_iter, CanonicalSerialize};

use blake2::Digest;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub fn hash_to_poly<F: PrimeField>(input: &[u8], degree: usize) -> DensePolynomial<F> {
    let input_hash: [u8; 32] = blake2::Blake2b::digest(input).try_into().unwrap();
    let coefficients = cfg_into_iter!(0..degree)
        .map(|i| {
            let mut input_with_counter = [0u8; 40];
            input_with_counter[..32].copy_from_slice(&input_hash);
            input_with_counter[32..].copy_from_slice(&i.to_le_bytes());
            F::from_bytes_le_mod_order(&blake2::Blake2b512::digest(input_with_counter))
        })
        .collect::<Vec<_>>();
    DensePolynomial::from_coefficients_vec(coefficients)
}

pub fn hash_commitment<E: PairingEngine>(cm: &Commitment<E>) -> E::Fr {
    let mut bytes = Vec::with_capacity(48);
    // This is faster than compressed serialization that's provided by `ToBytes`.
    cm.serialize_uncompressed(&mut bytes).unwrap();
    E::Fr::from_bytes_le_mod_order(&blake2::Blake2b512::digest(&bytes))
}

pub fn hash_commitments<E: PairingEngine>(cms: impl ExactSizeIterator<Item = Commitment<E>>) -> Vec<E::Fr> {
    let num_commitments = cms.len();
    let cm_bytes = cms
        .flat_map(|c| {
            let mut bytes = Vec::with_capacity(48);
            c.serialize_uncompressed(&mut bytes).unwrap();
            bytes
        })
        .collect::<Vec<_>>();
    let cm_hash = blake2::Blake2s256::digest(&cm_bytes);
    cfg_into_iter!(0..(num_commitments + 1))
        .map(|i| {
            let mut input_with_counter = [0u8; 40];
            input_with_counter[..32].copy_from_slice(&cm_hash);
            input_with_counter[32..].copy_from_slice(&i.to_le_bytes());
            E::Fr::from_bytes_le_mod_order(&blake2::Blake2b512::digest(input_with_counter))
        })
        .collect()
}
