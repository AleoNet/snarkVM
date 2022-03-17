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

use crate::polycommit::{BatchLCProof, PolynomialCommitment};

use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{self, Read, Write},
    serialize::*,
    FromBytes,
    ToBytes,
};

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitments<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> {
    /// Commitment to the `w` polynomial.
    pub w: PC::Commitment,
    /// Commitment to the `z_a` polynomial.
    pub z_a: PC::Commitment,
    /// Commitment to the `z_b` polynomial.
    pub z_b: PC::Commitment,
    /// Commitment to the masking polynomial.
    pub mask_poly: PC::Commitment,
    /// Commitment to the `g_1` polynomial.
    pub g_1: PC::Commitment,
    /// Commitment to the `h_1` polynomial.
    pub h_1: PC::Commitment,
    /// Commitment to the `g_a` polynomial.
    pub g_a: PC::Commitment,
    /// Commitment to the `g_b` polynomial.
    pub g_b: PC::Commitment,
    /// Commitment to the `g_c` polynomial.
    pub g_c: PC::Commitment,
    /// Commitment to the `h_2` polynomial.
    pub h_2: PC::Commitment,
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct EvaluationsForProof<F: PrimeField> {
    /// Evaluation of `z_a` at `beta`.
    pub z_a_eval: F,
    /// Evaluation of `z_b` at `beta`.
    pub z_b_eval: F,
    /// Evaluation of `g_1` at `beta`.
    pub g_1_eval: F,
    /// Evaluation of `t` at `beta`.
    pub t_eval: F,
    /// Evaluation of `g_a` at `beta`.
    pub g_a_eval: F,
    /// Evaluation of `g_b` at `gamma`.
    pub g_b_eval: F,
    /// Evaluation of `g_c` at `gamma`.
    pub g_c_eval: F,
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> {
    /// Commitments to prover polynomials.
    pub commitments: Commitments<F, CF, PC>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: EvaluationsForProof<F>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: BatchLCProof<F, CF, PC>,
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> Proof<F, CF, PC> {
    /// Construct a new proof.
    pub fn new(
        commitments: Commitments<F, CF, PC>,
        evaluations: EvaluationsForProof<F>,
        pc_proof: BatchLCProof<F, CF, PC>,
    ) -> Self {
        Self { commitments, evaluations, pc_proof }
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> ToBytes for Proof<F, CF, PC> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> FromBytes for Proof<F, CF, PC> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}
