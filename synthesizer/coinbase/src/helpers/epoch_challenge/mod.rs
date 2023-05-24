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

mod bytes;

use super::*;
use crate::hash_to_polynomial;
use snarkvm_algorithms::fft::Evaluations as EvaluationsOnDomain;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochChallenge<N: Network> {
    /// The epoch number.
    epoch_number: u32,
    /// The epoch block hash, defined as the block hash right before the epoch updated.
    epoch_block_hash: N::BlockHash,
    /// The epoch polynomial.
    epoch_polynomial: DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>,
    /// The evaluations of the epoch polynomial over the product domain.
    epoch_polynomial_evaluations: EvaluationsOnDomain<<N::PairingCurve as PairingEngine>::Fr>,
}

impl<N: Network> EpochChallenge<N> {
    /// Initializes a new epoch challenge.
    pub fn new(epoch_number: u32, epoch_block_hash: N::BlockHash, degree: u32) -> Result<Self> {
        // Construct the 'input' as '( epoch_number || epoch_block_hash )'
        let input: Vec<u8> = epoch_number.to_le_bytes().into_iter().chain(epoch_block_hash.to_bytes_le()?).collect();

        let product_domain = CoinbasePuzzle::<N>::product_domain(degree)?;

        let epoch_polynomial = hash_to_polynomial::<<N::PairingCurve as PairingEngine>::Fr>(&input, degree);
        ensure!(u32::try_from(epoch_polynomial.degree()).is_ok(), "Degree is too large");

        let epoch_polynomial_evaluations = epoch_polynomial.evaluate_over_domain_by_ref(product_domain);
        // Returns the epoch challenge.
        Ok(EpochChallenge { epoch_number, epoch_block_hash, epoch_polynomial, epoch_polynomial_evaluations })
    }

    /// Returns the epoch number for the solution.
    pub const fn epoch_number(&self) -> u32 {
        self.epoch_number
    }

    /// Returns the epoch block hash for the solution.
    pub const fn epoch_block_hash(&self) -> N::BlockHash {
        self.epoch_block_hash
    }

    /// Returns the epoch polynomial for the solution.
    pub const fn epoch_polynomial(&self) -> &DensePolynomial<<N::PairingCurve as PairingEngine>::Fr> {
        &self.epoch_polynomial
    }

    /// Returns the evaluations of the epoch polynomial over the product domain.
    pub const fn epoch_polynomial_evaluations(&self) -> &EvaluationsOnDomain<<N::PairingCurve as PairingEngine>::Fr> {
        &self.epoch_polynomial_evaluations
    }

    /// Returns the number of coefficients of the epoch polynomial.
    pub fn degree(&self) -> u32 {
        // Convert the degree into a u32.
        // The `unwrap` is guaranteed to succeed as we check the degree is less
        // than `u32::MAX` in `new`.
        u32::try_from(self.epoch_polynomial.degree()).unwrap()
    }

    /// Returns the number of coefficients of the epoch polynomial.
    pub fn num_coefficients(&self) -> Result<u32> {
        let degree = self.degree();
        degree.checked_add(1).ok_or_else(|| anyhow!("Epoch polynomial degree ({degree} + 1) overflows"))
    }
}
