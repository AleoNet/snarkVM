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

mod epoch_challenge;
pub use epoch_challenge::*;

mod partial_solution;
pub use partial_solution::*;

mod prover_solution;
pub use prover_solution::*;

mod puzzle_commitment;
pub use puzzle_commitment::*;

use crate::coinbase_puzzle::{hash_commitment, hash_commitments, CoinbasePuzzle};
use console::{account::Address, prelude::*, types::Field};
use snarkvm_algorithms::{
    fft::{domain::FFTPrecomputation, DensePolynomial, EvaluationDomain},
    polycommit::kzg10::{KZGCommitment, KZGProof, LagrangeBasis, VerifierKey, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::{
    borrow::Cow,
    io::{Read, Result as IoResult, Write},
};

/// The proof of opening the polynomial, for the solution.
pub type PuzzleProof<N> = KZGProof<<N as Environment>::PairingCurve>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PuzzleConfig {
    /// The maximum degree of the polynomial.
    pub degree: u32,
}

pub type CoinbaseVerifyingKey<N> = VerifierKey<<N as Environment>::PairingCurve>;

#[derive(Clone, Debug)]
pub struct CoinbaseProvingKey<N: Network> {
    /// The key used to commit to polynomials in Lagrange basis.
    pub lagrange_basis_at_beta_g: Vec<<N::PairingCurve as PairingEngine>::G1Affine>,
    /// Domain used to compute the product of the epoch polynomial and the prover polynomial.
    pub product_domain: EvaluationDomain<<N::PairingCurve as PairingEngine>::Fr>,
    /// Precomputation to speed up FFTs.
    pub fft_precomputation: FFTPrecomputation<<N::PairingCurve as PairingEngine>::Fr>,
    /// Elements of the product domain.
    pub product_domain_elements: Vec<<N::PairingCurve as PairingEngine>::Fr>,
    /// The verifying key of the coinbase puzzle.
    pub verifying_key: CoinbaseVerifyingKey<N>,
}

impl<N: Network> CoinbaseProvingKey<N> {
    /// Obtain elements of the SRS in the lagrange basis powers.
    pub fn lagrange_basis(&self) -> LagrangeBasis<N::PairingCurve> {
        LagrangeBasis {
            lagrange_basis_at_beta_g: Cow::Borrowed(self.lagrange_basis_at_beta_g.as_slice()),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
            domain: self.product_domain,
        }
    }

    /// Returns the elements of the product domain.
    pub fn product_domain_elements(&self) -> &[<N::PairingCurve as PairingEngine>::Fr] {
        &self.product_domain_elements
    }
}
