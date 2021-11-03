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
use snarkvm_algorithms::Prepare;
use snarkvm_fields::{ConstraintFieldError, PrimeField, ToConstraintField};
use snarkvm_polycommit::PolynomialCommitment;
use snarkvm_utilities::{error, errors::SerializationError, serialize::*, FromBytes, ToBytes, ToMinimalBits};

use crate::{Read, Write};
use derivative::Derivative;
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_r1cs::SynthesisError;

/// Verification key for a specific index (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CircuitVerifyingKey<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> {
    /// Stores information about the size of the circuit, as well as its defined field.
    pub circuit_info: CircuitInfo<F>,
    /// Commitments to the indexed polynomials.
    pub circuit_commitments: Vec<PC::Commitment>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: PC::VerifierKey,
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> ToBytes for CircuitVerifyingKey<F, CF, PC> {
    fn write_le<W: Write>(&self, mut w: W) -> crate::io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize CircuitVerifyingKey"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> ToMinimalBits for CircuitVerifyingKey<F, CF, PC> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        let domain_h = EvaluationDomain::<F>::new(self.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let domain_k = EvaluationDomain::<F>::new(self.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();

        assert!(domain_h.size() < u64::MAX as usize);
        assert!(domain_k.size() < u64::MAX as usize);

        let domain_h_size = domain_h.size() as u64;
        let domain_k_size = domain_k.size() as u64;

        let domain_h_size_bits = domain_h_size
            .to_le_bytes()
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();
        let domain_k_size_bits = domain_k_size
            .to_le_bytes()
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();

        let circuit_commitments_bits = self.circuit_commitments.to_minimal_bits();

        [domain_h_size_bits, domain_k_size_bits, circuit_commitments_bits].concat()
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> FromBytes for CircuitVerifyingKey<F, CF, PC> {
    fn read_le<R: Read>(mut r: R) -> crate::io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize CircuitVerifyingKey"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> CircuitVerifyingKey<F, CF, PC> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.circuit_commitments.iter()
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> From<CircuitProvingKey<F, CF, PC>>
    for CircuitVerifyingKey<F, CF, PC>
{
    fn from(other: CircuitProvingKey<F, CF, PC>) -> Self {
        other.circuit_verifying_key
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> From<PreparedCircuitVerifyingKey<F, CF, PC>>
    for CircuitVerifyingKey<F, CF, PC>
{
    fn from(other: PreparedCircuitVerifyingKey<F, CF, PC>) -> Self {
        other.orig_vk
    }
}

impl<F, CF, PC> Prepare<PreparedCircuitVerifyingKey<F, CF, PC>> for CircuitVerifyingKey<F, CF, PC>
where
    F: PrimeField,
    CF: PrimeField,
    PC: PolynomialCommitment<F, CF>,
{
    /// Prepare the circuit verifying key.
    fn prepare(&self) -> PreparedCircuitVerifyingKey<F, CF, PC> {
        let mut prepared_index_comms = Vec::<PC::PreparedCommitment>::new();
        for (_, comm) in self.circuit_commitments.iter().enumerate() {
            prepared_index_comms.push(comm.prepare());
        }

        let prepared_verifier_key = self.verifier_key.prepare();

        let domain_h = EvaluationDomain::<F>::new(self.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let domain_k = EvaluationDomain::<F>::new(self.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();

        let domain_h_size = domain_h.size();
        let domain_k_size = domain_k.size();

        PreparedCircuitVerifyingKey::<F, CF, PC> {
            domain_h_size: domain_h_size as u64,
            domain_k_size: domain_k_size as u64,
            prepared_index_comms,
            prepared_verifier_key,
            orig_vk: (*self).clone(),
        }
    }
}

impl<F, CF, PC> ToConstraintField<CF> for CircuitVerifyingKey<F, CF, PC>
where
    F: PrimeField,
    CF: PrimeField,
    PC: PolynomialCommitment<F, CF>,
{
    fn to_field_elements(&self) -> Result<Vec<CF>, ConstraintFieldError> {
        let domain_h = EvaluationDomain::<CF>::new(self.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let domain_k = EvaluationDomain::<CF>::new(self.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();

        let mut res = Vec::new();
        res.append(&mut CF::from(domain_h.size() as u128).to_field_elements()?);
        res.append(&mut CF::from(domain_k.size() as u128).to_field_elements()?);
        for comm in self.circuit_commitments.iter() {
            res.append(&mut comm.to_field_elements()?);
        }

        // Intentionally ignore the appending of the PC verifier key.

        Ok(res)
    }
}
