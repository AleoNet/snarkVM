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

use serde::{
    de::{Error as DeserializeError, SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize,
    Deserializer,
    Serialize,
    Serializer,
};
use std::{
    fmt::{
        Debug,
        Display,
        Formatter,
        {self},
    },
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
};

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
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
        }
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
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> FromBytes for Proof<F, CF, PC> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}

impl<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> Serialize for Proof<F, CF, PC> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let proof_bytes = self.to_bytes_le().expect("Failed to serialize proof bytes");

        let mut tup = s.serialize_tuple(proof_bytes.len() + 1)?;
        tup.serialize_element(&proof_bytes.len())?;

        for byte in proof_bytes.iter() {
            tup.serialize_element(byte)?;
        }

        tup.end()
    }
}

impl<'de, F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> Deserialize<'de> for Proof<F, CF, PC> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct ArrayVisitor<F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>>(PhantomData<(F, CF, PC)>);

        impl<'de, F: PrimeField, CF: PrimeField, PC: PolynomialCommitment<F, CF>> Visitor<'de> for ArrayVisitor<F, CF, PC> {
            type Value = Proof<F, CF, PC>;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                formatter.write_str("a valid proof")
            }

            fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<Proof<F, CF, PC>, S::Error> {
                let proof_size = seq
                    .next_element()?
                    .ok_or_else(|| DeserializeError::custom("could not read proof size"))?;

                let mut proof_bytes: Vec<u8> = vec![0u8; proof_size];

                for b in &mut proof_bytes[..] {
                    *b = seq
                        .next_element()?
                        .ok_or_else(|| DeserializeError::custom("could not read bytes"))?;
                }

                Ok(Proof::from_bytes_le(&proof_bytes).expect("Failed to deserialize proof bytes"))
            }
        }

        deserializer.deserialize_tuple(2, ArrayVisitor::<F, CF, PC>(PhantomData))
    }
}
