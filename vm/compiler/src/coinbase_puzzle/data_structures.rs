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

use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    polycommit::kzg10::{Commitment, LagrangeBasis, Powers, Proof, VerifierKey},
};
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{FromBytes, ToBytes};

use std::{
    borrow::Cow,
    collections::BTreeMap,
    io::{Read, Result as IoResult, Write},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PuzzleConfig {
    pub difficulty: usize,
    pub degree: usize,
}

pub type CoinbasePuzzleVerifyingKey<E> = VerifierKey<E>;

#[derive(Clone, Debug)]
pub struct CoinbasePuzzleProvingKey<E: PairingEngine> {
    /// The key used to commit to polynomials.
    pub powers_of_beta_g: Vec<E::G1Affine>,

    /// The key used to commit to polynomials in Lagrange basis.
    pub lagrange_bases_at_beta_g: BTreeMap<usize, Vec<E::G1Affine>>,

    pub vk: VerifierKey<E>,
}

impl<E: PairingEngine> CoinbasePuzzleProvingKey<E> {
    /// Obtain powers for the underlying KZG10 construction
    pub fn powers(&self) -> Powers<E> {
        Powers {
            powers_of_beta_g: self.powers_of_beta_g.as_slice().into(),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
        }
    }

    /// Obtain elements of the SRS in the lagrange basis powers.
    pub fn lagrange_basis(&self, domain: EvaluationDomain<E::Fr>) -> Option<LagrangeBasis<E>> {
        self.lagrange_bases_at_beta_g.get(&domain.size()).map(|basis| LagrangeBasis {
            lagrange_basis_at_beta_g: Cow::Borrowed(basis),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
            domain,
        })
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EpochInfo {
    pub epoch_number: u64,
}

impl EpochInfo {
    pub fn to_bytes_le(&self) -> [u8; 8] {
        self.epoch_number.to_le_bytes()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PlaceholderAddress(pub [u8; 32]);

impl PlaceholderAddress {
    pub fn to_bytes_le(&self) -> [u8; 32] {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochChallenge<E: PairingEngine> {
    pub epoch_polynomial: DensePolynomial<E::Fr>,
}

impl<E: PairingEngine> EpochChallenge<E> {
    pub fn degree(&self) -> usize {
        self.epoch_polynomial.degree()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProverPuzzleSolution<E: PairingEngine> {
    pub address: PlaceholderAddress,
    pub nonce: u64,
    pub commitment: Commitment<E>,
    pub proof: Proof<E>,
}

impl<E: PairingEngine> ToBytes for ProverPuzzleSolution<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.address.0.write_le(&mut writer)?;
        self.nonce.write_le(&mut writer)?;
        self.commitment.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<E: PairingEngine> FromBytes for ProverPuzzleSolution<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let address = PlaceholderAddress(FromBytes::read_le(&mut reader)?);
        let nonce = u64::read_le(&mut reader)?;
        let commitment = Commitment::read_le(&mut reader)?;
        let proof = Proof::read_le(&mut reader)?;

        Ok(Self { address, nonce, commitment, proof })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CombinedPuzzleSolution<E: PairingEngine> {
    pub individual_puzzle_solutions: Vec<(PlaceholderAddress, u64, Commitment<E>)>,
    pub proof: Proof<E>,
}

impl<E: PairingEngine> ToBytes for CombinedPuzzleSolution<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.individual_puzzle_solutions.len() as u32).write_le(&mut writer)?;

        for individual_puzzle_solution in &self.individual_puzzle_solutions {
            individual_puzzle_solution.0.0.write_le(&mut writer)?;
            individual_puzzle_solution.1.write_le(&mut writer)?;
            individual_puzzle_solution.2.write_le(&mut writer)?;
        }

        self.proof.write_le(&mut writer)
    }
}

impl<E: PairingEngine> FromBytes for CombinedPuzzleSolution<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let individual_puzzle_solutions_len: u32 = FromBytes::read_le(&mut reader)?;

        let mut individual_puzzle_solutions = Vec::with_capacity(individual_puzzle_solutions_len as usize);
        for _ in 0..individual_puzzle_solutions_len {
            let address = PlaceholderAddress(FromBytes::read_le(&mut reader)?);
            let nonce: u64 = FromBytes::read_le(&mut reader)?;
            let commitment: Commitment<E> = FromBytes::read_le(&mut reader)?;
            individual_puzzle_solutions.push((address, nonce, commitment));
        }

        let proof = Proof::read_le(&mut reader)?;

        Ok(Self { individual_puzzle_solutions, proof })
    }
}
