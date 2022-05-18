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
    fn serialize_with_mode<W: snarkvm_utilities::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for comm in &self.witness_commitments {
            comm.serialize_with_mode(&mut writer, compress)?;
        }
        CanonicalSerialize::serialize_with_mode(&self.mask_poly, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_1, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.h_1, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_a, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_b, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_c, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.h_2, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        size += self.witness_commitments.len()
            * CanonicalSerialize::serialized_size(&self.witness_commitments[0], compress);
        size += CanonicalSerialize::serialized_size(&self.mask_poly, compress);
        size += CanonicalSerialize::serialized_size(&self.g_1, compress);
        size += CanonicalSerialize::serialized_size(&self.h_1, compress);
        size += CanonicalSerialize::serialized_size(&self.g_a, compress);
        size += CanonicalSerialize::serialized_size(&self.g_b, compress);
        size += CanonicalSerialize::serialized_size(&self.g_c, compress);
        size += CanonicalSerialize::serialized_size(&self.h_2, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_size: usize,
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        let mut witness_commitments = Vec::new();
        for _ in 0..batch_size {
            witness_commitments.push(CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?);
        }
        Ok(Commitments {
            witness_commitments,
            mask_poly: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_b: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_c: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_2: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
        })
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
    fn serialize_with_mode<W: snarkvm_utilities::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for z_b_eval in &self.z_b_evals {
            CanonicalSerialize::serialize_with_mode(z_b_eval, &mut writer, compress)?;
        }
        CanonicalSerialize::serialize_with_mode(&self.g_1_eval, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_a_eval, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_b_eval, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_c_eval, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        size += self.z_b_evals.iter().map(|s| s.serialized_size(compress)).sum::<usize>();
        size += CanonicalSerialize::serialized_size(&self.g_1_eval, compress);
        size += CanonicalSerialize::serialized_size(&self.g_a_eval, compress);
        size += CanonicalSerialize::serialized_size(&self.g_b_eval, compress);
        size += CanonicalSerialize::serialized_size(&self.g_c_eval, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_size: usize,
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        let mut z_b_evals = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            z_b_evals.push(CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?);
        }
        Ok(Evaluations {
            z_b_evals,
            g_1_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_b_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_c_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}

impl<F: PrimeField> Evaluations<F> {
    pub(crate) fn from_map(map: &std::collections::BTreeMap<String, F>, batch_size: usize) -> Self {
        let z_b_evals = map.iter().filter_map(|(k, v)| k.starts_with("z_b_").then(|| *v)).collect::<Vec<_>>();
        assert_eq!(z_b_evals.len(), batch_size);
        Self { z_b_evals, g_1_eval: map["g_1"], g_a_eval: map["g_a"], g_b_eval: map["g_b"], g_c_eval: map["g_c"] }
    }

    pub(crate) fn get(&self, label: &str) -> Option<F> {
        if let Some(index) = label.strip_prefix("z_b_") {
            self.z_b_evals.get(index.parse::<usize>().unwrap()).copied()
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

impl<F: PrimeField> Valid for Evaluations<F> {
    fn check(&self) -> Result<(), snarkvm_utilities::SerializationError> {
        self.z_b_evals.check()?;
        self.g_1_eval.check()?;
        self.g_a_eval.check()?;
        self.g_b_eval.check()?;
        self.g_c_eval.check()
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
    fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize_with_mode(&self.batch_size, &mut writer, compress)?;
        Commitments::serialize_with_mode(&self.commitments, &mut writer, compress)?;
        Evaluations::serialize_with_mode(&self.evaluations, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.msg, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.pc_proof, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, mode: Compress) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.batch_size, mode);
        size += Commitments::serialized_size(&self.commitments, mode);
        size += Evaluations::serialized_size(&self.evaluations, mode);
        size += CanonicalSerialize::serialized_size(&self.msg, mode);
        size += CanonicalSerialize::serialized_size(&self.pc_proof, mode);
        size
    }
}

impl<E: PairingEngine> Valid for Proof<E> {
    fn check(&self) -> Result<(), SerializationError> {
        self.batch_size.check()?;
        self.commitments.check()?;
        self.evaluations.check()?;
        self.msg.check()?;
        self.pc_proof.check()
    }
}

impl<E: PairingEngine> CanonicalDeserialize for Proof<E> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let batch_size = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(Proof {
            batch_size,
            commitments: Commitments::deserialize_with_mode(batch_size, &mut reader, compress, validate)?,
            evaluations: Evaluations::deserialize_with_mode(batch_size, &mut reader, compress, validate)?,
            msg: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            pc_proof: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}

impl<E: PairingEngine> ToBytes for Proof<E> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        Self::serialize_compressed(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<E: PairingEngine> FromBytes for Proof<E> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        Self::deserialize_compressed(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}
