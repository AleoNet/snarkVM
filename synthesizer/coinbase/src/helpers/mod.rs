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

use crate::{hash_commitment, hash_commitments, CoinbasePuzzle};
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
