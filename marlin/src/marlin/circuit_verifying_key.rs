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
use snarkvm_curves::traits::PrimeField;
use snarkvm_polycommit::PolynomialCommitment;
use snarkvm_utilities::{
    bytes::{FromBytes, ToBytes},
    error,
    errors::SerializationError,
    serialize::*,
};

use derivative::Derivative;
use std::io::{self, Read, Write};

/// Verification key for a specific index (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CircuitVerifyingKey<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// Stores information about the size of the circuit, as well as its defined field.
    pub circuit_info: CircuitInfo<F>,
    /// Commitments to the indexed polynomials.
    pub circuit_commitments: Vec<PC::Commitment>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: PC::VerifierKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> ToBytes for CircuitVerifyingKey<F, PC> {
    fn write<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize CircuitVerifyingKey"))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> FromBytes for CircuitVerifyingKey<F, PC> {
    fn read<R: Read>(mut r: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize CircuitVerifyingKey"))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> CircuitVerifyingKey<F, PC> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.circuit_commitments.iter()
    }
}
