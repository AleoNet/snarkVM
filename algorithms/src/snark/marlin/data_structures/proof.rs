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

use crate::{polycommit::sonic_pc, snark::marlin::{ahp, Circuit, MarlinMode}, SNARKError};

use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{self, Read, Write},
    serialize::*,
    FromBytes,
    ToBytes,
};

use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitments<E: PairingEngine> {
    pub witness_commitments: Vec<WitnessCommitments<E>>,
    /// Commitment to the masking polynomial.
    pub mask_poly: Option<sonic_pc::Commitment<E>>,
    /// Commitment to the `g_1` polynomial.
    pub g_1: sonic_pc::Commitment<E>,
    /// Commitment to the `h_1` polynomial.
    pub h_1: sonic_pc::Commitment<E>,
    /// Commitment to the `g_a` polynomials.
    pub g_a_commitments: Vec<sonic_pc::Commitment<E>>,
    /// Commitment to the `g_b` polynomials.
    pub g_b_commitments: Vec<sonic_pc::Commitment<E>>,
    /// Commitment to the `g_c` polynomials.
    pub g_c_commitments: Vec<sonic_pc::Commitment<E>>,
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
        for comm in &self.g_a_commitments {
            comm.serialize_with_mode(&mut writer, compress)?;
        }
        for comm in &self.g_b_commitments {
            comm.serialize_with_mode(&mut writer, compress)?;
        }
        for comm in &self.g_c_commitments {
            comm.serialize_with_mode(&mut writer, compress)?;
        }
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
        size += self.g_a_commitments.len()
            * CanonicalSerialize::serialized_size(&self.g_a_commitments[0], compress);
        size += self.g_b_commitments.len()
            * CanonicalSerialize::serialized_size(&self.g_b_commitments[0], compress);
        size += self.g_c_commitments.len()
            * CanonicalSerialize::serialized_size(&self.g_c_commitments[0], compress);
        size += CanonicalSerialize::serialized_size(&self.h_2, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_size: usize,
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        let deserialize_batch = |size| { (0..size).map(|| CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?).collect()? };
        Ok(Commitments {
            witness_commitments: deserialize_batch(batch_size),
            mask_poly: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_commitments: deserialize_batch(batch_size),
            g_b_commitments: deserialize_batch(batch_size),
            g_c_commitments: deserialize_batch(batch_size),
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

// TODO: we're deserializing this, should we still keep references to objects...?
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluations<'a, F: PrimeField, MM: MarlinMode> {
    /// Evaluations of `z_b_i_j`'s at `beta`.
    pub z_b_evals: BTreeMap<&'a Circuit<F, MM>, Vec<F>>,
    /// Evaluation of `g_1` at `beta`.
    pub g_1_eval: F,
    /// Evaluation of `g_a_i`'s at `beta`.
    pub g_a_evals: BTreeMap<&'a Circuit<F, MM>, F>,
    /// Evaluation of `g_b_i`'s at `gamma`.
    pub g_b_evals: BTreeMap<&'a Circuit<F, MM>, F>,
    /// Evaluation of `g_c_i`'s at `gamma`.
    pub g_c_evals: BTreeMap<&'a Circuit<F, MM>, F>,
}

impl<'a, F: PrimeField, MM: MarlinMode> Evaluations<'a, F, MM> {
    fn serialize_with_mode<W: snarkvm_utilities::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        self.z_b_evals.map(|z_b_eval| CanonicalSerialize::serialize_with_mode(z_b_eval, &mut writer, compress)?).collect()?;
        CanonicalSerialize::serialize_with_mode(&self.g_1_eval, &mut writer, compress)?;
        self.g_a_evals.map(|z_b_eval| CanonicalSerialize::serialize_with_mode(z_b_eval, &mut writer, compress)?).collect()?;
        self.g_b_evals.map(|z_b_eval| CanonicalSerialize::serialize_with_mode(z_b_eval, &mut writer, compress)?).collect()?;
        self.g_c_evals.map(|z_b_eval| CanonicalSerialize::serialize_with_mode(z_b_eval, &mut writer, compress)?).collect()?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        size += self.z_b_evals.iter().map(|s| s.serialized_size(compress)).sum::<usize>();
        size += CanonicalSerialize::serialized_size(&self.g_1_eval, compress);
        size += self.g_a_eval.iter().map(|s| s.serialized_size(compress)).sum::<usize>();
        size += self.g_b_eval.iter().map(|s| s.serialized_size(compress)).sum::<usize>();
        size += self.g_c_eval.iter().map(|s| s.serialized_size(compress)).sum::<usize>();
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_size: usize,
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        let deserialize_batch = |size| { (0..size).map(|| CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?).collect()? };
        Ok(Evaluations {
            z_b_evals: deserialize_batch(batch_size),
            g_1_eval: deserialize_batch(1)[0],
            g_a_evals: deserialize_batch(batch_size),
            g_b_evals: deserialize_batch(batch_size),
            g_c_evals: deserialize_batch(batch_size),
        })
    }
}

impl<'a, F: PrimeField, MM: MarlinMode> Evaluations<'a, F, MM> {
    pub(crate) fn from_map(map: &std::collections::BTreeMap<String, F>, batch_sizes: BTreeMap<&'a Circuit<F, MM>, usize>) -> Self {
        let z_b_evals = map.iter().filter_map(|(k, v)| k.contains("z_b_").then_some(*v) ).collect::<Vec<_>>();
        assert_eq!(z_b_evals.len(), batch_sizes.map(|_,s|s).sum());
        let g_a_evals = map.iter().filter_map(|(k, v)| k.contains("g_a_").then_some(*v) ).collect::<Vec<_>>();
        let g_b_evals = map.iter().filter_map(|(k, v)| k.contains("g_b_").then_some(*v) ).collect::<Vec<_>>();
        let g_c_evals = map.iter().filter_map(|(k, v)| k.contains("g_c_").then_some(*v) ).collect::<Vec<_>>();
        Self { z_b_evals, g_1_eval: map["g_1"], g_a_evals, g_b_evals, g_c_evals }
    }

    pub(crate) fn get(&self, label: &str) -> Option<F> {
        let circuit_id = label.split(" ").collect::<Vec<&str>>()[0];
        if let Some(index) = label.contains("z_b_") {
            self.get_from_evaluations(&self.z_b_evals, circuit_id, index)
        } else if let Some(index) = label.contains("g_a_") {
            self.get_from_evaluations(&self.g_a_evals, circuit_id, index)
        } else if let Some(index) = label.contains("g_b_") {
            self.get_from_evaluations(&self.g_b_evals, circuit_id, index)
        } else if let Some(index) = label.contains("g_c_") {
            self.get_from_evaluations(&self.g_c_evals, circuit_id, index)
        } else {
            match label {
                "g_1" => Some(self.g_1_eval),
                _ => None,
            }
        }
    }

    // TODO: index type is probably incorrect
    fn get_from_evaluations(evaluations_to_iter: &BTreeMap<&Circuit<F, MM>, Vec<F>>, circuit_id: &str, index: usize) -> Option<F> {
        for (circuit, evaluations) in evaluations_to_iter.iter() {
            if format!("{:x?}", circuit.hash) == circuit_id {
                evaluations.get(index.parse::<usize>().unwrap()).copied();
            }
        }
    }    
}

impl<'a, F: PrimeField, MM: MarlinMode> Valid for Evaluations<'a, F, MM> {
    fn check(&self) -> Result<(), snarkvm_utilities::SerializationError> {
        self.z_b_evals.check()?;
        self.g_1_eval.check()?;
        self.g_a_eval.check()?;
        self.g_b_eval.check()?;
        self.g_c_eval.check()
    }
}

impl<'a, F: PrimeField, MM: MarlinMode> Evaluations<'a, F, MM> {
    pub fn to_field_elements(&self) -> Vec<F> {
        let mut result = self.z_b_evals.clone();
        result.extend([self.g_1_eval, self.g_a_eval, self.g_b_eval, self.g_c_eval]);
        result
    }
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<'a, E: PairingEngine, MM: MarlinMode> {
    /// The number of instances being proven in this proof.
    batch_size: usize,

    /// Commitments to prover polynomials.
    pub commitments: Commitments<E>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: Evaluations<'a, E::Fr, MM>,

    /// Prover message: sum_a, sum_b, sum_c for each instance
    pub msg: ahp::prover::ThirdMessage<'a, E::Fr, MM>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: sonic_pc::BatchLCProof<E>,
}

impl<'a, E: PairingEngine, MM: MarlinMode> Proof<'a, E, MM> {
    /// Construct a new proof.
    pub fn new(
        batch_size: usize,
        commitments: Commitments<E>,
        evaluations: Evaluations<'a, E::Fr, MM>,
        msg: ahp::prover::ThirdMessage<'a, E::Fr, MM>,
        pc_proof: sonic_pc::BatchLCProof<E>,
    ) -> Result<Self, SNARKError> {
        if commitments.witness_commitments.len() != batch_size {
            return Err(SNARKError::BatchSizeMismatch);
        }
        if evaluations.z_b_evals.len() != batch_size {
            return Err(SNARKError::BatchSizeMismatch);
        }
        Ok(Self { batch_size, commitments, evaluations, msg, pc_proof })
    }

    pub fn batch_size(&self) -> Result<usize, SNARKError> {
        if self.commitments.witness_commitments.len() != self.batch_size {
            return Err(SNARKError::BatchSizeMismatch);
        }
        if self.evaluations.z_b_evals.len() != self.batch_size {
            return Err(SNARKError::BatchSizeMismatch);
        }
        Ok(self.batch_size)
    }
}

impl<'a, E: PairingEngine, MM: MarlinMode> CanonicalSerialize for Proof<'a, E, MM> {
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

impl<'a, E: PairingEngine, MM: MarlinMode> Valid for Proof<'a, E, MM> {
    fn check(&self) -> Result<(), SerializationError> {
        self.batch_size.check()?;
        self.commitments.check()?;
        self.evaluations.check()?;
        self.msg.check()?;
        self.pc_proof.check()
    }
}

impl<'a, E: PairingEngine, MM: MarlinMode> CanonicalDeserialize for Proof<'a, E, MM> {
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

impl<'a, E: PairingEngine, MM: MarlinMode> ToBytes for Proof<'a, E, MM> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        Self::serialize_compressed(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<'a, E: PairingEngine, MM: MarlinMode> FromBytes for Proof<'a, E, MM> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        Self::deserialize_compressed(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}
