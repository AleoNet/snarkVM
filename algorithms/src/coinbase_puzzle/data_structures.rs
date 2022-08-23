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

use crate::{
    fft::EvaluationDomain,
    polycommit::kzg10::{Commitment, LagrangeBasis, Powers, Proof, VerifierKey},
};
use snarkvm_curves::PairingEngine;
use std::{borrow::Cow, collections::BTreeMap};

use crate::fft::DensePolynomial;

pub use crate::polycommit::kzg10::UniversalParams as SRS;
pub type VerifyingKey<E> = VerifierKey<E>;

#[derive(Clone, Debug)]
pub struct ProvingKey<E: PairingEngine> {
    /// The key used to commit to polynomials.
    pub powers_of_beta_g: Vec<E::G1Affine>,

    /// The key used to commit to polynomials in Lagrange basis.
    pub lagrange_bases_at_beta_g: BTreeMap<usize, Vec<E::G1Affine>>,

    pub vk: VerifierKey<E>,
}

impl<E: PairingEngine> ProvingKey<E> {
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
    pub address: Address,
    pub nonce: u64,
    pub commitment: Commitment<E>,
    pub proof: Proof<E>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CombinedPuzzleSolution<E: PairingEngine> {
    pub individual_puzzle_solutions: Vec<(Address, u64, Commitment<E>)>,
    pub proof: Proof<E>,
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
pub struct Address(pub [u8; 32]);

impl Address {
    pub fn to_bytes_le(&self) -> [u8; 32] {
        self.0
    }
}
