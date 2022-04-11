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

use crate::{polycommit::sonic_pc, snark::marlin::ahp};

use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{self, Read, Write},
    serialize::*,
    FromBytes,
    ToBytes,
};

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitments<E: PairingEngine> {
    pub witness_commitments: Vec<WitnessCommitments<E>>,
    /// Commitment to the masking polynomial.
    pub mask_poly: Option<sonic_pc::Commitment<E>>,
    /// Commitment to the `g_1` polynomial.
    pub g_1: sonic_pc::Commitment<E>,
    /// Commitment to the `h_1` polynomial.
    pub h_1: sonic_pc::Commitment<E>,
    /// Commitment to the `g_a` polynomial.
    pub g_a: sonic_pc::Commitment<E>,
    /// Commitment to the `g_b` polynomial.
    pub g_b: sonic_pc::Commitment<E>,
    /// Commitment to the `g_c` polynomial.
    pub g_c: sonic_pc::Commitment<E>,
    /// Commitment to the `h_2` polynomial.
    pub h_2: sonic_pc::Commitment<E>,
}

impl<E: PairingEngine> Commitments<E> {
    fn serialize<W: snarkvm_utilities::Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for comm in &self.witness_commitments {
            comm.serialize(writer)?;
        }
        CanonicalSerialize::serialize(&self.mask_poly, writer)?;
        CanonicalSerialize::serialize(&self.g_1, writer)?;
        CanonicalSerialize::serialize(&self.h_1, writer)?;
        CanonicalSerialize::serialize(&self.g_a, writer)?;
        CanonicalSerialize::serialize(&self.g_b, writer)?;
        CanonicalSerialize::serialize(&self.g_c, writer)?;
        CanonicalSerialize::serialize(&self.h_2, writer)?;
        Ok(())
    }

    fn serialized_size(&self) -> usize {
        let mut size = 0;
        size += self.witness_commitments.len() * CanonicalSerialize::serialized_size(&self.witness_commitments[0]);
        size += CanonicalSerialize::serialized_size(&self.mask_poly);
        size += CanonicalSerialize::serialized_size(&self.g_1);
        size += CanonicalSerialize::serialized_size(&self.h_1);
        size += CanonicalSerialize::serialized_size(&self.g_a);
        size += CanonicalSerialize::serialized_size(&self.g_b);
        size += CanonicalSerialize::serialized_size(&self.g_c);
        size += CanonicalSerialize::serialized_size(&self.h_2);
        size
    }

    fn serialize_uncompressed<W: snarkvm_utilities::Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for comm in &self.witness_commitments {
            comm.serialize_uncompressed(writer)?;
        }
        CanonicalSerialize::serialize_uncompressed(&self.mask_poly, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_1, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.h_1, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_a, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_b, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_c, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.h_2, writer)?;
        Ok(())
    }

    fn uncompressed_size(&self) -> usize {
        let mut size = 0;
        size += self.witness_commitments.len() * CanonicalSerialize::uncompressed_size(&self.witness_commitments[0]);
        size += CanonicalSerialize::uncompressed_size(&self.mask_poly);
        size += CanonicalSerialize::uncompressed_size(&self.g_1);
        size += CanonicalSerialize::uncompressed_size(&self.h_1);
        size += CanonicalSerialize::uncompressed_size(&self.g_a);
        size += CanonicalSerialize::uncompressed_size(&self.g_b);
        size += CanonicalSerialize::uncompressed_size(&self.g_c);
        size += CanonicalSerialize::uncompressed_size(&self.h_2);
        size
    }

    fn deserialize<R: snarkvm_utilities::Read>(
        batch_size: usize,
        reader: &mut R,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        {
            let mut witness_commitments = Vec::with_capacity(batch_size);
            for _ in 0..batch_size {
                witness_commitments.push(CanonicalDeserialize::deserialize(reader)?);
            }
            Ok(Commitments {
                witness_commitments,
                mask_poly: CanonicalDeserialize::deserialize(reader)?,
                g_1: CanonicalDeserialize::deserialize(reader)?,
                h_1: CanonicalDeserialize::deserialize(reader)?,
                g_a: CanonicalDeserialize::deserialize(reader)?,
                g_b: CanonicalDeserialize::deserialize(reader)?,
                g_c: CanonicalDeserialize::deserialize(reader)?,
                h_2: CanonicalDeserialize::deserialize(reader)?,
            })
        }
    }

    fn deserialize_uncompressed<R: snarkvm_utilities::Read>(
        batch_size: usize,
        reader: &mut R,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        {
            let mut witness_commitments = Vec::with_capacity(batch_size);
            for _ in 0..batch_size {
                witness_commitments.push(CanonicalDeserialize::deserialize_uncompressed(reader)?);
            }
            Ok(Commitments {
                witness_commitments,
                mask_poly: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_1: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                h_1: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_a: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_b: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_c: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                h_2: CanonicalDeserialize::deserialize_uncompressed(reader)?,
            })
        }
    }
}
/// Commitments to the `w`, `z_a`, and `z_b` polynomials.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct WitnessCommitments<E: PairingEngine> {
    /// Commitment to the `w` polynomial.
    pub w: sonic_pc::Commitment<E>,
    /// Commitment to the `z_a` polynomial.
    pub z_a: sonic_pc::Commitment<E>,
    /// Commitment to the `z_b` polynomial.
    pub z_b: sonic_pc::Commitment<E>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluations<F: PrimeField> {
    /// Evaluation of `z_b_i`'s at `beta`.
    pub z_b_evals: Vec<F>,
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
    fn serialize<W: snarkvm_utilities::Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for z_b_eval in &self.z_b_evals {
            CanonicalSerialize::serialize(z_b_eval, writer)?;
        }
        CanonicalSerialize::serialize(&self.g_1_eval, writer)?;
        CanonicalSerialize::serialize(&self.g_a_eval, writer)?;
        CanonicalSerialize::serialize(&self.g_b_eval, writer)?;
        CanonicalSerialize::serialize(&self.g_c_eval, writer)?;
        Ok(())
    }

    fn serialized_size(&self) -> usize {
        let mut size = 0;
        size += self.z_b_evals.len() * CanonicalSerialize::serialized_size(&self.z_b_evals[0]);
        size += CanonicalSerialize::serialized_size(&self.g_1_eval);
        size += CanonicalSerialize::serialized_size(&self.g_a_eval);
        size += CanonicalSerialize::serialized_size(&self.g_b_eval);
        size += CanonicalSerialize::serialized_size(&self.g_c_eval);
        size
    }

    fn serialize_uncompressed<W: snarkvm_utilities::Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for z_b_eval in &self.z_b_evals {
            CanonicalSerialize::serialize_uncompressed(z_b_eval, writer)?;
        }
        CanonicalSerialize::serialize_uncompressed(&self.g_1_eval, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_a_eval, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_b_eval, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.g_c_eval, writer)?;
        Ok(())
    }

    fn uncompressed_size(&self) -> usize {
        let mut size = 0;
        size += self.z_b_evals.len() * CanonicalSerialize::uncompressed_size(&self.z_b_evals[0]);
        size += CanonicalSerialize::uncompressed_size(&self.g_1_eval);
        size += CanonicalSerialize::uncompressed_size(&self.g_a_eval);
        size += CanonicalSerialize::uncompressed_size(&self.g_b_eval);
        size += CanonicalSerialize::uncompressed_size(&self.g_c_eval);
        size
    }

    fn deserialize<R: snarkvm_utilities::Read>(
        batch_size: usize,
        reader: &mut R,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        {
            let mut z_b_evals = Vec::with_capacity(batch_size);
            for _ in 0..batch_size {
                z_b_evals.push(CanonicalDeserialize::deserialize(reader)?);
            }
            Ok(Evaluations {
                z_b_evals,
                g_1_eval: CanonicalDeserialize::deserialize(reader)?,
                g_a_eval: CanonicalDeserialize::deserialize(reader)?,
                g_b_eval: CanonicalDeserialize::deserialize(reader)?,
                g_c_eval: CanonicalDeserialize::deserialize(reader)?,
            })
        }
    }

    fn deserialize_uncompressed<R: snarkvm_utilities::Read>(
        batch_size: usize,
        reader: &mut R,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        {
            let mut z_b_evals = Vec::with_capacity(batch_size);
            for _ in 0..batch_size {
                z_b_evals.push(CanonicalDeserialize::deserialize_uncompressed(reader)?);
            }
            Ok(Evaluations {
                z_b_evals,
                g_1_eval: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_a_eval: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_b_eval: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                g_c_eval: CanonicalDeserialize::deserialize_uncompressed(reader)?,
            })
        }
    }
}

impl<F: PrimeField> Evaluations<F> {
    pub(crate) fn from_map(map: &std::collections::BTreeMap<String, F>, batch_size: usize) -> Self {
        let z_b_evals = map.iter().filter_map(|(k, v)| k.starts_with("z_b_").then(|| *v)).collect::<Vec<_>>();
        assert_eq!(z_b_evals.len(), batch_size);
        Self { z_b_evals, g_1_eval: map["g_1"], g_a_eval: map["g_a"], g_b_eval: map["g_b"], g_c_eval: map["g_c"] }
    }

    pub(crate) fn get(&self, label: &str) -> Option<F> {
        if label.starts_with("z_b_") {
            self.z_b_evals.get(label[5..].parse::<usize>().unwrap()).copied()
        } else {
            match label {
                "g_1" => Some(self.g_1_eval),
                "g_a" => Some(self.g_a_eval),
                "g_b" => Some(self.g_b_eval),
                "g_c" => Some(self.g_c_eval),
                _ => None,
            }
        }
    }
}

impl<F: PrimeField> Evaluations<F> {
    pub fn to_field_elements(&self) -> Vec<F> {
        let mut result = self.z_b_evals.clone();
        result.extend([self.g_1_eval, self.g_a_eval, self.g_b_eval, self.g_c_eval]);
        result
    }
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E: PairingEngine> {
    /// The number of instances being proven in this proof.
    batch_size: usize,

    /// Commitments to prover polynomials.
    pub commitments: Commitments<E>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: Evaluations<E::Fr>,

    /// Prover message: sum_a, sum_b, sum_c
    pub msg: ahp::prover::ThirdMessage<E::Fr>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: sonic_pc::BatchLCProof<E>,
}

impl<E: PairingEngine> Proof<E> {
    /// Construct a new proof.
    pub fn new(
        batch_size: usize,
        commitments: Commitments<E>,
        evaluations: Evaluations<E::Fr>,
        msg: ahp::prover::ThirdMessage<E::Fr>,
        pc_proof: sonic_pc::BatchLCProof<E>,
    ) -> Self {
        Self { batch_size, commitments, evaluations, msg, pc_proof }
    }
}

impl<E: PairingEngine> CanonicalSerialize for Proof<E> {
    fn serialize<W: snarkvm_utilities::Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        CanonicalSerialize::serialize(&self.batch_size, writer)?;
        Commitments::serialize(&self.commitments, writer)?;
        Evaluations::serialize(&self.evaluations, writer)?;
        CanonicalSerialize::serialize(&self.msg, writer)?;
        CanonicalSerialize::serialize(&self.pc_proof, writer)?;
        Ok(())
    }

    fn serialized_size(&self) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.batch_size);
        size += Commitments::serialized_size(&self.commitments);
        size += Evaluations::serialized_size(&self.evaluations);
        size += CanonicalSerialize::serialized_size(&self.msg);
        size += CanonicalSerialize::serialized_size(&self.pc_proof);
        size
    }

    fn serialize_uncompressed<W: snarkvm_utilities::Write>(
        &self,
        writer: &mut W,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        CanonicalSerialize::serialize_uncompressed(&self.batch_size, writer)?;
        Commitments::serialize_uncompressed(&self.commitments, writer)?;
        Evaluations::serialize_uncompressed(&self.evaluations, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.msg, writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.pc_proof, writer)?;
        Ok(())
    }

    fn uncompressed_size(&self) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::uncompressed_size(&self.batch_size);
        size += Commitments::uncompressed_size(&self.commitments);
        size += Evaluations::uncompressed_size(&self.evaluations);
        size += CanonicalSerialize::uncompressed_size(&self.msg);
        size += CanonicalSerialize::uncompressed_size(&self.pc_proof);
        size
    }
}

impl<E: PairingEngine> CanonicalDeserialize for Proof<E> {
    fn deserialize<R: snarkvm_utilities::Read>(reader: &mut R) -> Result<Self, snarkvm_utilities::SerializationError> {
        {
            let batch_size = CanonicalDeserialize::deserialize(reader)?;
            Ok(Proof {
                batch_size,
                commitments: Commitments::deserialize(batch_size, reader)?,
                evaluations: Evaluations::deserialize(batch_size, reader)?,
                msg: CanonicalDeserialize::deserialize(reader)?,
                pc_proof: CanonicalDeserialize::deserialize(reader)?,
            })
        }
    }

    fn deserialize_uncompressed<R: snarkvm_utilities::Read>(
        reader: &mut R,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        {
            let batch_size = CanonicalDeserialize::deserialize(reader)?;
            Ok(Proof {
                batch_size,
                commitments: Commitments::deserialize_uncompressed(batch_size, reader)?,
                evaluations: Evaluations::deserialize_uncompressed(batch_size, reader)?,
                msg: CanonicalDeserialize::deserialize_uncompressed(reader)?,
                pc_proof: CanonicalDeserialize::deserialize_uncompressed(reader)?,
            })
        }
    }
}

impl<E: PairingEngine> ToBytes for Proof<E> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<E: PairingEngine> FromBytes for Proof<E> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        CanonicalDeserialize::deserialize(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}
