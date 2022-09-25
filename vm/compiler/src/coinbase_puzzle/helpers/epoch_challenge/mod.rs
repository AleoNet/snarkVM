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

mod bytes;

use super::*;
use crate::coinbase_puzzle::hash_to_polynomial;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochChallenge<N: Network> {
    /// The epoch number.
    epoch_number: u64,
    /// The epoch block hash, defined as the block hash right before the epoch updated.
    epoch_block_hash: N::BlockHash,
    /// The epoch polynomial.
    epoch_polynomial: DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>,
}

impl<N: Network> EpochChallenge<N> {
    /// Initializes a new epoch challenge.
    pub fn new(epoch_number: u64, epoch_block_hash: N::BlockHash, degree: u32) -> Result<Self> {
        // Construct the 'input' as '( epoch_number || epoch_block_hash )'
        let input: Vec<u8> =
            epoch_number.to_le_bytes().into_iter().chain(epoch_block_hash.to_bytes_le()?.into_iter()).collect();
        // Returns the epoch challenge.
        Ok(EpochChallenge {
            epoch_number,
            epoch_block_hash,
            epoch_polynomial: hash_to_polynomial::<<N::PairingCurve as PairingEngine>::Fr>(&input, degree)?,
        })
    }

    /// Returns the epoch number for the solution.
    pub const fn epoch_number(&self) -> u64 {
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

    /// Returns the degree of the epoch polynomial.
    pub fn degree(&self) -> Result<u32> {
        // Retrieve the degree of the epoch polynomial.
        let degree = match self.epoch_polynomial.degree().checked_add(1) {
            Some(degree) => degree,
            None => bail!("Epoch polynomial degree ({} + 1) overflows", self.epoch_polynomial.degree()),
        };
        // Cast the degree into a u32.
        match u32::try_from(degree) {
            Ok(degree) => Ok(degree),
            Err(_) => bail!("Epoch polynomial degree ({}) is too large", self.epoch_polynomial.degree()),
        }
    }
}
