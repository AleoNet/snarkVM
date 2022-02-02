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

use crate::{
    ahp::indexer::*,
    marlin::{CircuitVerifyingKey, MarlinMode},
    IoResult,
    Read,
    Vec,
    Write,
};
use snarkvm_algorithms::polycommit::PolynomialCommitment;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{serialize::*, FromBytes, ToBytes};

use derivative::Derivative;

/// Proving key for a specific circuit (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derive(Debug)]
pub struct CircuitProvingKey<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>, MM: MarlinMode> {
    /// The circuit verifying key.
    pub circuit_verifying_key: CircuitVerifyingKey<F, CF, PC, MM>,
    /// The randomness for the circuit polynomial commitments.
    pub circuit_commitment_randomness: Vec<PC::Randomness>,
    /// The circuit itself.
    pub circuit: Circuit<F, MM>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: PC::CommitterKey,
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>, MM: MarlinMode> ToBytes
    for CircuitProvingKey<F, CF, PC, MM>
{
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        CanonicalSerialize::serialize(&self.circuit_verifying_key, &mut writer)?;
        CanonicalSerialize::serialize(&self.circuit_commitment_randomness, &mut writer)?;
        CanonicalSerialize::serialize(&self.circuit, &mut writer)?;

        self.committer_key.write_le(&mut writer)
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>, MM: MarlinMode> FromBytes
    for CircuitProvingKey<F, CF, PC, MM>
{
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let circuit_verifying_key = CanonicalDeserialize::deserialize(&mut reader)?;
        let circuit_commitment_randomness = CanonicalDeserialize::deserialize(&mut reader)?;
        let circuit = CanonicalDeserialize::deserialize(&mut reader)?;
        let committer_key: PC::CommitterKey = FromBytes::read_le(&mut reader)?;

        Ok(Self { circuit_verifying_key, circuit_commitment_randomness, circuit, committer_key })
    }
}
