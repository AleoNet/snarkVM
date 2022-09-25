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

mod coinbase_solution;
pub use coinbase_solution::*;

mod partial_solution;
pub use partial_solution::*;

mod prover_solution;
pub use prover_solution::*;

use crate::coinbase_puzzle::{hash_commitment, hash_commitments, hash_to_poly, CoinbasePuzzle};
use console::{account::Address, prelude::*};
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    msm::VariableBase,
    polycommit::kzg10::{KZGCommitment, KZGProof, LagrangeBasis, Powers, VerifierKey, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::{
    borrow::Cow,
    collections::BTreeMap,
    io::{Read, Result as IoResult, Write},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PuzzleConfig {
    /// The maximum degree of the polynomial.
    pub degree: u32,
}

pub type CoinbasePuzzleVerifyingKey<N> = VerifierKey<<N as Environment>::PairingCurve>;

#[derive(Clone, Debug)]
pub struct CoinbasePuzzleProvingKey<N: Network> {
    /// The key used to commit to polynomials.
    pub powers_of_beta_g: Vec<<N::PairingCurve as PairingEngine>::G1Affine>,

    /// The key used to commit to polynomials in Lagrange basis.
    pub lagrange_bases_at_beta_g: BTreeMap<usize, Vec<<N::PairingCurve as PairingEngine>::G1Affine>>,

    pub vk: CoinbasePuzzleVerifyingKey<N>,
}

impl<N: Network> CoinbasePuzzleProvingKey<N> {
    /// Obtain powers for the underlying KZG10 construction
    pub fn powers(&self) -> Powers<N::PairingCurve> {
        Powers {
            powers_of_beta_g: self.powers_of_beta_g.as_slice().into(),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
        }
    }

    /// Obtain elements of the SRS in the lagrange basis powers.
    pub fn lagrange_basis(
        &self,
        domain: EvaluationDomain<<N::PairingCurve as PairingEngine>::Fr>,
    ) -> Option<LagrangeBasis<N::PairingCurve>> {
        self.lagrange_bases_at_beta_g.get(&domain.size()).map(|basis| LagrangeBasis {
            lagrange_basis_at_beta_g: Cow::Borrowed(basis),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
            domain,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochChallenge<N: Network> {
    /// The epoch number.
    pub epoch_number: u64,
    /// The epoch block hash, defined as the block hash right before the epoch updated.
    pub epoch_block_hash: N::BlockHash,
    /// The epoch polynomial.
    pub epoch_polynomial: DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>,
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
            epoch_polynomial: hash_to_poly::<<N::PairingCurve as PairingEngine>::Fr>(&input, degree)?,
        })
    }

    /// Returns the degree of the epoch polynomial.
    pub fn degree(&self) -> u32 {
        match u32::try_from(self.epoch_polynomial.degree()) {
            Ok(degree) => degree,
            Err(_) => N::halt(format!("Epoch polynomial degree ({}) is too large", self.epoch_polynomial.degree())),
        }
    }
}

impl<N: Network> FromBytes for EpochChallenge<N> {
    /// Reads the epoch challenge from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the epoch number.
        let epoch_number = FromBytes::read_le(&mut reader)?;
        // Read the epoch block hash.
        let epoch_block_hash = FromBytes::read_le(&mut reader)?;
        // Read the epoch degree.
        let degree = FromBytes::read_le(&mut reader)?;
        // Return the epoch challenge.
        Self::new(epoch_number, epoch_block_hash, degree).map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for EpochChallenge<N> {
    /// Writes the epoch challenge to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the epoch number.
        self.epoch_number.write_le(&mut writer)?;
        // Write the epoch block hash.
        self.epoch_block_hash.write_le(&mut writer)?;
        // Write the epoch degree.
        self.degree().write_le(&mut writer)
    }
}
