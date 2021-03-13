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

use crate::{ahp::indexer::*, marlin::CircuitVerifyingKey, Vec};
use snarkvm_fields::PrimeField;
use snarkvm_polycommit::PolynomialCommitment;
use snarkvm_utilities::{errors::SerializationError, serialize::*, FromBytes, ToBytes};

use derivative::Derivative;
use std::io::{Read, Result as IoResult, Write};

/// Proving key for a specific circuit (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CircuitProvingKey<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// The circuit verifying key.
    pub circuit_verifying_key: CircuitVerifyingKey<F, PC>,
    /// The randomness for the circuit polynomial commitments.
    pub circuit_commitment_randomness: Vec<PC::Randomness>,
    /// The circuit itself.
    pub circuit: Circuit<F>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: PC::CommitterKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> ToBytes for CircuitProvingKey<F, PC> {
    fn write<W: Write>(&self, mut _writer: W) -> IoResult<()> {
        unimplemented!()
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> FromBytes for CircuitProvingKey<F, PC> {
    #[inline]
    fn read<R: Read>(mut _reader: R) -> IoResult<Self> {
        unimplemented!()
    }
}
