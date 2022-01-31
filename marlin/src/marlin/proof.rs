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

use crate::{ahp::prover::ProverMessage, Vec};
use snarkvm_fields::PrimeField;
use snarkvm_polycommit::{BatchLCProof, PCCommitment, PolynomialCommitment};
use snarkvm_utilities::{error, errors::SerializationError, serialize::*, FromBytes, ToBytes};

use crate::{Read, Write};

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub commitments: Vec<Vec<PC::Commitment>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<F>,
    /// The field elements sent by the prover.
    pub prover_messages: Vec<ProverMessage<F>>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: BatchLCProof<F, CF, PC>,
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> Proof<F, CF, PC> {
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<PC::Commitment>>,
        evaluations: Vec<F>,
        prover_messages: Vec<ProverMessage<F>>,
        pc_proof: BatchLCProof<F, CF, PC>,
    ) -> Self {
        Self { commitments, evaluations, prover_messages, pc_proof }
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        let size_of_fe_in_bytes = F::zero().to_repr().as_ref().len() * 8;
        let mut num_comms_without_degree_bounds = 0;
        let mut num_comms_with_degree_bounds = 0;
        let mut size_bytes_comms_without_degree_bounds = 0;
        let mut size_bytes_comms_with_degree_bounds = 0;
        let mut size_bytes_proofs = 0;
        for c in self.commitments.iter().flatten() {
            if !c.has_degree_bound() {
                num_comms_without_degree_bounds += 1;
                size_bytes_comms_without_degree_bounds += c.serialized_size();
            } else {
                num_comms_with_degree_bounds += 1;
                size_bytes_comms_with_degree_bounds += c.serialized_size();
            }
        }

        let proofs: Vec<PC::Proof> = self.pc_proof.proof.clone().into();
        let num_proofs = proofs.len();
        for proof in &proofs {
            size_bytes_proofs += proof.serialized_size();
        }

        let num_evaluations = self.evaluations.len();
        let evaluation_size_in_bytes = num_evaluations * size_of_fe_in_bytes;
        let num_prover_messages: usize = self.prover_messages.iter().map(|v| v.field_elements.len()).sum();
        let prover_message_size_in_bytes = num_prover_messages * size_of_fe_in_bytes;
        let argument_size = size_bytes_comms_with_degree_bounds
            + size_bytes_comms_without_degree_bounds
            + size_bytes_proofs
            + prover_message_size_in_bytes
            + evaluation_size_in_bytes;
        let statistics = format!(
            "Argument size in bytes: {}\n\n\
             Number of commitments without degree bounds: {}\n\
             Size (in bytes) of commitments without degree bounds: {}\n\
             Number of commitments with degree bounds: {}\n\
             Size (in bytes) of commitments with degree bounds: {}\n\n\
             Number of evaluation proofs: {}\n\
             Size (in bytes) of evaluation proofs: {}\n\n\
             Number of evaluations: {}\n\
             Size (in bytes) of evaluations: {}\n\n\
             Number of field elements in prover messages: {}\n\
             Size (in bytes) of prover message: {}\n",
            argument_size,
            num_comms_without_degree_bounds,
            size_bytes_comms_without_degree_bounds,
            num_comms_with_degree_bounds,
            size_bytes_comms_with_degree_bounds,
            num_proofs,
            size_bytes_proofs,
            num_evaluations,
            evaluation_size_in_bytes,
            num_prover_messages,
            prover_message_size_in_bytes,
        );
        add_to_trace!(|| "Statistics about proof", || statistics);
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> ToBytes for Proof<F, CF, PC> {
    fn write_le<W: Write>(&self, mut w: W) -> crate::io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> FromBytes for Proof<F, CF, PC> {
    fn read_le<R: Read>(mut r: R) -> crate::io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}
