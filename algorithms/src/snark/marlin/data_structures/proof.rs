// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::{polycommit::sonic_pc, snark::marlin::{ahp, CircuitId}, SNARKError};

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
        Ok(Commitments {
            witness_commitments: (0..batch_size).map(|_| {
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)
                }).collect::<Result<_,_>>()?,
            mask_poly: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_commitments: (0..batch_size).map(|_| {
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)
                }).collect::<Result<_,_>>()?,
            g_b_commitments: (0..batch_size).map(|_| {
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)
                }).collect::<Result<_,_>>()?,
            g_c_commitments: (0..batch_size).map(|_| {
                    CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)
                }).collect::<Result<_,_>>()?,
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
    /// Evaluations of `z_b_i_j`'s at `beta`.
    pub z_b_evals: BTreeMap<CircuitId, Vec<F>>,
    /// Evaluation of `g_1` at `beta`.
    pub g_1_eval: F,
    /// Evaluation of `g_a_i`'s at `beta`.
    pub g_a_evals: BTreeMap<CircuitId, F>,
    /// Evaluation of `g_b_i`'s at `gamma`.
    pub g_b_evals: BTreeMap<CircuitId, F>,
    /// Evaluation of `g_c_i`'s at `gamma`.
    pub g_c_evals: BTreeMap<CircuitId, F>,
}

impl<'a, F: PrimeField> Evaluations<F> {
    fn serialize_with_mode<W: snarkvm_utilities::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        CanonicalSerialize::serialize_with_mode(&self.z_b_evals, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_1_eval, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_a_evals, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_b_evals, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_c_evals, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.z_b_evals, compress);
        size += CanonicalSerialize::serialized_size(&self.g_1_eval, compress);
        size += CanonicalSerialize::serialized_size(&self.g_a_evals, compress);
        size += CanonicalSerialize::serialized_size(&self.g_b_evals, compress);
        size += CanonicalSerialize::serialized_size(&self.g_c_evals, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        Ok(Evaluations {
            z_b_evals: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_1_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_evals: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_b_evals: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_c_evals: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}

impl<'a, F: PrimeField> Evaluations<F> {
    pub(crate) fn from_map(map: &std::collections::BTreeMap<String, F>, batch_sizes: BTreeMap<CircuitId, usize>) -> Self {
        let mut z_b_evals: BTreeMap<CircuitId, Vec<F>> = BTreeMap::new();
        let mut g_a_evals = BTreeMap::new();
        let mut g_b_evals = BTreeMap::new();
        let mut g_c_evals = BTreeMap::new();
        
        for (label, value) in map {
            if label == "g_1" {
                break
            }
            
            let circuit_id = CircuitId::from_witness_label(label);
            if label.contains("z_b_") {
                if let Some(z_b_i) = z_b_evals.get_mut(&circuit_id) {
                    z_b_i.push(*value);
                } else {
                    let mut values = Vec::with_capacity(batch_sizes[&circuit_id]);
                    values.push(*value);
                    z_b_evals.insert(circuit_id, values);
                }
            } else if label.contains("g_a") {
                g_a_evals.insert(circuit_id, *value);
            } else if label.contains("g_b") {
                g_b_evals.insert(circuit_id, *value);
            } else if label.contains("g_c") {
                g_c_evals.insert(circuit_id, *value);
            }
        }
        Self { z_b_evals, g_1_eval: map["g_1"], g_a_evals, g_b_evals, g_c_evals }
    }

    pub(crate) fn get(&self, label: &str) -> Option<F> {
        if label == "g_1" {
            return Some(self.g_1_eval)
        }

        let circuit_id = CircuitId::from_witness_label(label);
        if let Some(index) = label.find("z_b_") {
            if let Some(z_b_eval) = self.z_b_evals.get(&circuit_id) {
                let j = label[index + 4..].parse::<usize>().unwrap();
                Some(z_b_eval[j])
            } else {
                None
            }
        } else if let Some(_) = label.find("g_a") {
            self.g_a_evals.get(&circuit_id).copied()
        } else if let Some(_) = label.find("g_b") {
            self.g_b_evals.get(&circuit_id).copied()
        } else if let Some(_) = label.find("g_c") {
            self.g_c_evals.get(&circuit_id).copied()
        } else {
            None
        }
    }
}

impl<'a, F: PrimeField> Valid for Evaluations<F> {
    fn check(&self) -> Result<(), snarkvm_utilities::SerializationError> {
        self.z_b_evals.check()?;
        self.g_1_eval.check()?;
        self.g_a_evals.check()?;
        self.g_b_evals.check()?;
        self.g_c_evals.check()
    }
}

impl<'a, F: PrimeField> Evaluations<F> {
    pub fn to_field_elements(&self) -> Vec<F> {
        let mut result = self.z_b_evals.iter().flat_map(|(_,e)|e.clone()).collect::<Vec<F>>();
        result.extend([self.g_1_eval]);
        result.extend(self.g_a_evals.iter().map(|(_,e)|e.clone()));
        result.extend(self.g_b_evals.iter().map(|(_,e)|e.clone()));
        result.extend(self.g_c_evals.iter().map(|(_,e)|e.clone()));
        result
    }
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E: PairingEngine> {
    /// The number of instances being proven in this proof.
    batch_sizes: BTreeMap<CircuitId, usize>,

    /// Commitments to prover polynomials.
    pub commitments: Commitments<E>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: Evaluations<E::Fr>,

    /// Prover message: sum_a, sum_b, sum_c for each instance
    pub msg: ahp::prover::ThirdMessage<E::Fr>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: sonic_pc::BatchLCProof<E>,
}

impl<'a, E: PairingEngine> Proof<E> {
    /// Construct a new proof.
    pub fn new(
        batch_sizes: BTreeMap<CircuitId, usize>,
        total_instances: usize,
        commitments: Commitments<E>,
        evaluations: Evaluations<E::Fr>,
        msg: ahp::prover::ThirdMessage<E::Fr>,
        pc_proof: sonic_pc::BatchLCProof<E>,
    ) -> Result<Self, SNARKError> {
        if commitments.witness_commitments.len() != total_instances {
            return Err(SNARKError::BatchSizeMismatch);
        }
        for (circuit_id, z_b_evals_i) in evaluations.z_b_evals.iter() {
            if z_b_evals_i.len() != batch_sizes[circuit_id] {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }
        Ok(Self { batch_sizes, commitments, evaluations, msg, pc_proof })
    }

    pub fn batch_sizes(&self) -> Result<&BTreeMap<CircuitId, usize>, SNARKError> {
        let mut total_instances = 0;
        for (z_b_evals_i, batch_size) in self.evaluations.z_b_evals.values().zip(self.batch_sizes.values()) {
            total_instances += batch_size;
            if z_b_evals_i.len() != *batch_size {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }
        if self.commitments.witness_commitments.len() != total_instances {
            return Err(SNARKError::BatchSizeMismatch);
        }
        Ok(&self.batch_sizes)
    }
}

impl<'a, E: PairingEngine> CanonicalSerialize for Proof<E> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize_with_mode(&self.batch_sizes, &mut writer, compress)?;
        Commitments::serialize_with_mode(&self.commitments, &mut writer, compress)?;
        Evaluations::serialize_with_mode(&self.evaluations, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.msg, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.pc_proof, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, mode: Compress) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.batch_sizes, mode);
        size += Commitments::serialized_size(&self.commitments, mode);
        size += Evaluations::serialized_size(&self.evaluations, mode);
        size += CanonicalSerialize::serialized_size(&self.msg, mode);
        size += CanonicalSerialize::serialized_size(&self.pc_proof, mode);
        size
    }
}

impl<'a, E: PairingEngine> Valid for Proof<E> {
    fn check(&self) -> Result<(), SerializationError> {
        self.batch_sizes.check()?;
        self.commitments.check()?;
        self.evaluations.check()?;
        self.msg.check()?;
        self.pc_proof.check()
    }
}

impl<'a, E: PairingEngine> CanonicalDeserialize for Proof<E> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let batch_sizes: BTreeMap<CircuitId, usize> = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let total_batch_size = batch_sizes.iter().map(|(_,s)|s).sum();
        Ok(Proof {
            batch_sizes,
            commitments: Commitments::deserialize_with_mode(total_batch_size, &mut reader, compress, validate)?,
            evaluations: Evaluations::deserialize_with_mode(&mut reader, compress, validate)?,
            msg: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            pc_proof: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}

impl<'a, E: PairingEngine> ToBytes for Proof<E> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        Self::serialize_compressed(self, &mut w).map_err(|_| error("could not serialize Proof"))
    }
}

impl<'a, E: PairingEngine> FromBytes for Proof<E> {
    fn read_le<R: Read>(mut r: R) -> io::Result<Self> {
        Self::deserialize_compressed(&mut r).map_err(|_| error("could not deserialize Proof"))
    }
}
