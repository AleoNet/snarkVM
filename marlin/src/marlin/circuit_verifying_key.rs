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
    fiat_shamir::{FiatShamirError, FiatShamirRng},
    marlin::{CircuitProvingKey, PreparedCircuitVerifyingKey},
    Vec,
};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_polycommit::PolynomialCommitment;
use snarkvm_utilities::{error, errors::SerializationError, serialize::*, FromBytes, ToBytes};

use derivative::Derivative;
use std::io::{
    Read,
    Write,
    {self},
};

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
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize CircuitVerifyingKey"))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> FromBytes for CircuitVerifyingKey<F, PC> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize CircuitVerifyingKey"))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> CircuitVerifyingKey<F, PC> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.circuit_commitments.iter()
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> From<CircuitProvingKey<F, PC>> for CircuitVerifyingKey<F, PC> {
    fn from(other: CircuitProvingKey<F, PC>) -> Self {
        other.circuit_verifying_key
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> From<PreparedCircuitVerifyingKey<F, PC>>
    for CircuitVerifyingKey<F, PC>
{
    fn from(other: PreparedCircuitVerifyingKey<F, PC>) -> Self {
        other.orig_vk
    }
}

/// Compute the hash of the circuit verifying key.
pub(crate) fn compute_vk_hash<TargetField, BaseField, PC, FS>(
    vk: &CircuitVerifyingKey<TargetField, PC>,
) -> Result<Vec<BaseField>, FiatShamirError>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
{
    let mut vk_hash_rng = FS::new();
    vk_hash_rng.absorb_native_field_elements(&vk.circuit_commitments);
    vk_hash_rng.squeeze_native_field_elements(1)
}
