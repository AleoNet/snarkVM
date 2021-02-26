// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{ahp::indexer::*, Vec};
use snarkvm_errors::serialization::SerializationError;
use snarkvm_models::curves::PrimeField;
use snarkvm_polycommit::PolynomialCommitment;
use snarkvm_utilities::{
    bytes::{FromBytes, ToBytes},
    error,
    serialize::*,
};

use derivative::Derivative;
use std::io::{self, Read, Write};

/* ************************************************************************* */

/// The universal public parameters for the argument system.
pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F>>::UniversalParams;

/* ************************************************************************* */

/// Proving key for a specific index (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexProverKey<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// The index verifier key.
    pub index_vk: IndexVerifierKey<F, PC>,
    /// The randomness for the index polynomial commitments.
    pub index_comm_rands: Vec<PC::Randomness>,
    /// The index itself.
    pub index: Index<F>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: PC::CommitterKey,
}

/* ************************************************************************* */

/// Verification key for a specific index (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexVerifierKey<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<F>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<PC::Commitment>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: PC::VerifierKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> ToBytes for IndexVerifierKey<F, PC> {
    fn write<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize IndexVerifierKey"))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> FromBytes for IndexVerifierKey<F, PC> {
    fn read<R: Read>(mut r: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize IndexVerifierKey"))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> IndexVerifierKey<F, PC> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.index_comms.iter()
    }
}
