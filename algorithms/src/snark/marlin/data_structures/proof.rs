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

use crate::{
    polycommit::sonic_pc,
    snark::marlin::{ahp, CircuitId},
    SNARKError,
};

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
        serialize_vec_without_len(self.witness_commitments.iter(), &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.mask_poly, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.g_1, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.h_1, &mut writer, compress)?;
        serialize_vec_without_len(self.g_a_commitments.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_b_commitments.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_c_commitments.iter(), &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.h_2, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        size += serialized_vec_size_without_len(&self.witness_commitments, compress);
        size += CanonicalSerialize::serialized_size(&self.mask_poly, compress);
        size += CanonicalSerialize::serialized_size(&self.g_1, compress);
        size += CanonicalSerialize::serialized_size(&self.h_1, compress);
        size += serialized_vec_size_without_len(&self.g_a_commitments, compress);
        size += serialized_vec_size_without_len(&self.g_b_commitments, compress);
        size += serialized_vec_size_without_len(&self.g_c_commitments, compress);
        size += CanonicalSerialize::serialized_size(&self.h_2, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_sizes: &[usize],
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        let mut w = Vec::with_capacity(batch_sizes.iter().sum());
        for batch_size in batch_sizes {
            w.extend(deserialize_vec_without_len(&mut reader, compress, validate, *batch_size)?);
        }
        Ok(Commitments {
            witness_commitments: w,
            mask_poly: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_commitments: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_b_commitments: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_c_commitments: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
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
    pub z_b_evals: Vec<Vec<F>>,
    /// Evaluation of `g_1` at `beta`.
    pub g_1_eval: F,
    /// Evaluation of `g_a_i`'s at `beta`.
    pub g_a_evals: Vec<F>,
    /// Evaluation of `g_b_i`'s at `gamma`.
    pub g_b_evals: Vec<F>,
    /// Evaluation of `g_c_i`'s at `gamma`.
    pub g_c_evals: Vec<F>,
}

impl<F: PrimeField> Evaluations<F> {
    fn serialize_with_mode<W: snarkvm_utilities::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        for z_b_eval_circuit in &self.z_b_evals {
            serialize_vec_without_len(z_b_eval_circuit.iter(), &mut writer, compress)?;
        }
        CanonicalSerialize::serialize_with_mode(&self.g_1_eval, &mut writer, compress)?;
        serialize_vec_without_len(self.g_a_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_b_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_c_evals.iter(), &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        for z_b_eval_circuit in &self.z_b_evals {
            size += serialized_vec_size_without_len(z_b_eval_circuit, compress);
        }
        size += CanonicalSerialize::serialized_size(&self.g_1_eval, compress);
        size += serialized_vec_size_without_len(&self.g_a_evals, compress);
        size += serialized_vec_size_without_len(&self.g_b_evals, compress);
        size += serialized_vec_size_without_len(&self.g_c_evals, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_sizes: &[usize],
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        Ok(Evaluations {
            z_b_evals: batch_sizes
                .iter()
                .map(|batch_size| deserialize_vec_without_len(&mut reader, compress, validate, *batch_size))
                .collect::<Result<_, _>>()?,
            g_1_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_b_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_c_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
        })
    }
}

impl<F: PrimeField> Evaluations<F> {
    pub(crate) fn from_map(
        map: &std::collections::BTreeMap<String, F>,
        batch_sizes: BTreeMap<CircuitId, usize>,
    ) -> Self {
        let mut z_b_evals_collect: BTreeMap<CircuitId, Vec<F>> = BTreeMap::new();
        let mut g_a_evals = Vec::with_capacity(batch_sizes.len());
        let mut g_b_evals = Vec::with_capacity(batch_sizes.len());
        let mut g_c_evals = Vec::with_capacity(batch_sizes.len());

        for (label, value) in map {
            if label == "g_1" {
                break;
            }

            let circuit_id = CircuitId::from_witness_label(label);
            if label.contains("z_b_") {
                if let Some(z_b_i) = z_b_evals_collect.get_mut(&circuit_id) {
                    z_b_i.push(*value);
                } else {
                    let mut values = Vec::with_capacity(batch_sizes[&circuit_id]);
                    values.push(*value);
                    z_b_evals_collect.insert(circuit_id, values);
                }
            } else if label.contains("g_a") {
                g_a_evals.push(*value);
            } else if label.contains("g_b") {
                g_b_evals.push(*value);
            } else if label.contains("g_c") {
                g_c_evals.push(*value);
            }
        }
        let z_b_evals = z_b_evals_collect.into_values().collect();
        Self { z_b_evals, g_1_eval: map["g_1"], g_a_evals, g_b_evals, g_c_evals }
    }

    pub(crate) fn get(&self, circuit_index: usize, label: &str) -> Option<F> {
        if label == "g_1" {
            return Some(self.g_1_eval);
        }

        if let Some(index) = label.find("z_b_") {
            let z_b_eval_circuit = &self.z_b_evals[circuit_index];
            let instance_index = label[index + 4..].parse::<usize>().unwrap();
            z_b_eval_circuit.get(instance_index).copied()
        } else if label.contains("g_a") {
            self.g_a_evals.get(circuit_index).copied()
        } else if label.contains("g_b") {
            self.g_b_evals.get(circuit_index).copied()
        } else if label.contains("g_c") {
            self.g_c_evals.get(circuit_index).copied()
        } else {
            None
        }
    }

    pub fn to_field_elements(&self) -> Vec<F> {
        let mut result: Vec<F> = self.z_b_evals.iter().flatten().copied().collect();
        result.push(self.g_1_eval);
        result.extend_from_slice(&self.g_a_evals);
        result.extend_from_slice(&self.g_b_evals);
        result.extend_from_slice(&self.g_c_evals);
        result
    }
}

impl<F: PrimeField> Valid for Evaluations<F> {
    fn check(&self) -> Result<(), snarkvm_utilities::SerializationError> {
        self.z_b_evals.check()?;
        self.g_1_eval.check()?;
        self.g_a_evals.check()?;
        self.g_b_evals.check()?;
        self.g_c_evals.check()
    }
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E: PairingEngine> {
    /// The number of instances being proven in this proof.
    batch_sizes: Vec<usize>,

    /// Commitments to prover polynomials.
    pub commitments: Commitments<E>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: Evaluations<E::Fr>,

    /// Prover message: sum_a, sum_b, sum_c for each instance
    pub msg: ahp::prover::ThirdMessage<E::Fr>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: sonic_pc::BatchLCProof<E>,
}

impl<E: PairingEngine> Proof<E> {
    /// Construct a new proof.
    pub fn new(
        batch_sizes: BTreeMap<CircuitId, usize>,
        commitments: Commitments<E>,
        evaluations: Evaluations<E::Fr>,
        msg: ahp::prover::ThirdMessage<E::Fr>,
        pc_proof: sonic_pc::BatchLCProof<E>,
    ) -> Result<Self, SNARKError> {
        let mut total_instances = 0;
        let batch_sizes: Vec<usize> = batch_sizes.into_values().collect();
        for (z_b_evals, batch_size) in evaluations.z_b_evals.iter().zip(&batch_sizes) {
            total_instances += batch_size;
            if z_b_evals.len() != *batch_size {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }
        if commitments.witness_commitments.len() != total_instances {
            return Err(SNARKError::BatchSizeMismatch);
        }
        Ok(Self { batch_sizes, commitments, evaluations, msg, pc_proof })
    }

    pub fn batch_sizes(&self) -> Result<&[usize], SNARKError> {
        let mut total_instances = 0;
        for (z_b_evals_i, &batch_size) in self.evaluations.z_b_evals.iter().zip(self.batch_sizes.iter()) {
            total_instances += batch_size;
            if z_b_evals_i.len() != batch_size {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }
        if self.commitments.witness_commitments.len() != total_instances {
            return Err(SNARKError::BatchSizeMismatch);
        }
        Ok(&self.batch_sizes)
    }
}

impl<E: PairingEngine> CanonicalSerialize for Proof<E> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
        let batch_sizes: Vec<u64> = self.batch_sizes.iter().map(|x| u64::try_from(*x)).collect::<Result<_, _>>()?;
        CanonicalSerialize::serialize_with_mode(&batch_sizes, &mut writer, compress)?;
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

impl<E: PairingEngine> Valid for Proof<E> {
    fn check(&self) -> Result<(), SerializationError> {
        self.batch_sizes.check()?;
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
        let batch_sizes: Vec<u64> = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let batch_sizes: Vec<usize> = batch_sizes.into_iter().map(|x| x as usize).collect();
        Ok(Proof {
            commitments: Commitments::deserialize_with_mode(&batch_sizes, &mut reader, compress, validate)?,
            evaluations: Evaluations::deserialize_with_mode(&batch_sizes, &mut reader, compress, validate)?,
            msg: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            pc_proof: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            batch_sizes,
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

#[cfg(test)]
mod test {
    #![allow(non_camel_case_types)]

    use super::*;

    use crate::{
        polycommit::{
            kzg10::{KZGCommitment, KZGProof},
            sonic_pc::BatchProof,
        },
        snark::marlin::prover::MatrixSums,
    };
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fr, G1Affine},
        AffineCurve,
    };
    use snarkvm_utilities::{TestRng, Uniform};

    const fn modes() -> [(Compress, Validate); 4] {
        [
            (Compress::No, Validate::No),
            (Compress::Yes, Validate::No),
            (Compress::No, Validate::Yes),
            (Compress::Yes, Validate::Yes),
        ]
    }

    fn sample_commit() -> KZGCommitment<Bls12_377> {
        let buf = G1Affine::prime_subgroup_generator().to_bytes_le().unwrap();
        FromBytes::read_le(buf.as_slice()).unwrap()
    }

    fn rand_commitments(i: usize, j: usize, test_with_none: bool) -> Commitments<Bls12_377> {
        assert!(i > 0);
        assert!(j > 0);
        let sample_commit = sample_commit();
        let mask_poly = if test_with_none { None } else { Some(sample_commit) };
        Commitments {
            witness_commitments: vec![
                WitnessCommitments { w: sample_commit, z_a: sample_commit, z_b: sample_commit };
                i * j
            ],
            mask_poly,
            g_1: sample_commit,
            h_1: sample_commit,
            g_a_commitments: vec![sample_commit; j],
            g_b_commitments: vec![sample_commit; j],
            g_c_commitments: vec![sample_commit; j],
            h_2: sample_commit,
        }
    }

    fn rand_evaluations<F: PrimeField>(rng: &mut TestRng, i: usize, j: usize) -> Evaluations<F> {
        Evaluations {
            z_b_evals: vec![vec![F::rand(rng); i]; j],
            g_1_eval: F::rand(rng),
            g_a_evals: vec![F::rand(rng); j],
            g_b_evals: vec![F::rand(rng); j],
            g_c_evals: vec![F::rand(rng); j],
        }
    }

    fn rand_sums<F: PrimeField>(rng: &mut TestRng) -> MatrixSums<F> {
        MatrixSums::<F> { sum_a: F::rand(rng), sum_b: F::rand(rng), sum_c: F::rand(rng) }
    }

    fn rand_kzg_proof(rng: &mut TestRng, test_with_none: bool) -> KZGProof<Bls12_377> {
        let random_v = if test_with_none { None } else { Some(Fr::rand(rng)) };
        KZGProof::<Bls12_377> { w: G1Affine::prime_subgroup_generator(), random_v }
    }

    #[test]
    fn test_serializing_commitments() {
        for i in 1..11 {
            for j in 1..11 {
                let test_with_none = i * j % 2 == 0;
                let commitments = rand_commitments(i, j, test_with_none);
                let batch_sizes = vec![i; j];
                let combinations = modes();
                for (compress, validate) in combinations {
                    let size = Commitments::serialized_size(&commitments, compress);
                    let mut serialized = vec![0; size];
                    Commitments::serialize_with_mode(&commitments, &mut serialized[..], compress).unwrap();
                    let de =
                        Commitments::deserialize_with_mode(&batch_sizes, &serialized[..], compress, validate).unwrap();
                    assert_eq!(commitments, de);
                }
            }
        }
    }

    #[test]
    fn test_serializing_evaluations() {
        let rng = &mut TestRng::default();

        for i in 1..11 {
            for j in 1..11 {
                let evaluations: Evaluations<Fr> = rand_evaluations(rng, i, j);
                let batch_sizes = vec![i; j];
                let combinations = modes();
                for (compress, validate) in combinations {
                    let size = Evaluations::serialized_size(&evaluations, compress);
                    let mut serialized = vec![0; size];
                    Evaluations::serialize_with_mode(&evaluations, &mut serialized[..], compress).unwrap();
                    let de =
                        Evaluations::deserialize_with_mode(&batch_sizes, &serialized[..], compress, validate).unwrap();
                    assert_eq!(evaluations, de);
                }
            }
        }
    }

    #[test]
    fn test_serializing_proof() {
        let rng = &mut snarkvm_utilities::rand::TestRng::default();

        for i in 1..11 {
            for j in 1..11 {
                let test_with_none = i * j % 2 == 0;
                let batch_sizes = vec![i; j];
                let commitments = rand_commitments(i, j, test_with_none);
                let evaluations: Evaluations<Fr> = rand_evaluations(rng, i, j);
                let msg = ahp::prover::ThirdMessage::<Fr> { sums: vec![rand_sums(rng); j] };
                let mut proof_evaluations = None;
                if !test_with_none {
                    proof_evaluations = Some(vec![Fr::rand(rng); j]);
                }
                let pc_proof = sonic_pc::BatchLCProof {
                    proof: BatchProof(vec![rand_kzg_proof(rng, test_with_none); j]),
                    evaluations: proof_evaluations,
                };
                let proof = Proof { batch_sizes, commitments, evaluations, msg, pc_proof };
                let combinations = modes();
                for (compress, validate) in combinations {
                    let size = Proof::serialized_size(&proof, compress);
                    let mut serialized = vec![0; size];
                    Proof::serialize_with_mode(&proof, &mut serialized[..], compress).unwrap();
                    let de = Proof::deserialize_with_mode(&serialized[..], compress, validate).unwrap();
                    assert_eq!(proof, de);
                }
            }
        }
    }
}
