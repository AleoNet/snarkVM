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
    polycommit::{BatchLCProof, PolynomialCommitment},
    snark::marlin::ahp,
};

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
    pub mask_poly: Option<PC::Commitment>,
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
pub struct Evaluations<F: PrimeField> {
    /// Evaluation of `z_b` at `beta`.
    pub z_b_eval: F,
    /// Evaluation of `g_1` at `beta`.
    pub g_1_eval: F,
    /// Evaluation of `g_a` at `beta`.
    pub g_a_eval: F,
    /// Evaluation of `g_b` at `gamma`.
    pub g_b_eval: F,
    /// Evaluation of `g_c` at `gamma`.
    pub g_c_eval: F,
}

impl<F: PrimeField> Evaluations<F> {
    pub(crate) fn from_map(map: &std::collections::BTreeMap<String, F>) -> Self {
        Self {
            z_b_eval: map["z_b"],
            g_1_eval: map["g_1"],
            g_a_eval: map["g_a"],
            g_b_eval: map["g_b"],
            g_c_eval: map["g_c"],
        }
    }

    pub(crate) fn get(&self, label: &str) -> Option<F> {
        match label {
            "z_b" => Some(self.z_b_eval),
            "g_1" => Some(self.g_1_eval),
            "g_a" => Some(self.g_a_eval),
            "g_b" => Some(self.g_b_eval),
            "g_c" => Some(self.g_c_eval),
            _ => None,
        }
    }
}

impl<F: PrimeField> Evaluations<F> {
    pub fn to_field_elements(&self) -> [F; 5] {
        [self.z_b_eval, self.g_1_eval, self.g_a_eval, self.g_b_eval, self.g_c_eval]
    }
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> {
    /// Commitments to prover polynomials.
    pub commitments: Commitments<F, CF, PC>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: Evaluations<F>,

    /// Prover message: sum_a, sum_b, sum_c
    pub msg: ahp::prover::ThirdMessage<F>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: BatchLCProof<F, CF, PC>,
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> Proof<F, CF, PC> {
    /// Construct a new proof.
    pub fn new(
        commitments: Commitments<F, CF, PC>,
        evaluations: Evaluations<F>,
        msg: ahp::prover::ThirdMessage<F>,
        pc_proof: BatchLCProof<F, CF, PC>,
    ) -> Self {
        Self { commitments, evaluations, msg, pc_proof }
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
