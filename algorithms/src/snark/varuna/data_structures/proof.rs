// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    polycommit::sonic_pc,
    snark::varuna::{ahp, CircuitId},
    SNARKError,
};

use ahp::prover::{FourthMessage, ThirdMessage};
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

/// Commitments to the `w` and `multiplicities` polynomials.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct WitnessCommitments<E: PairingEngine> {
    /// Commitment to the `w` polynomial.
    pub w: sonic_pc::Commitment<E>,
    /// Commitment to the `multiplicities` polynomial.
    pub multiplicities: Option<sonic_pc::Commitment<E>>,
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitments<E: PairingEngine> {
    pub witness_commitments: Vec<WitnessCommitments<E>>,
    /// Commitment to the masking polynomial for rowcheck.
    pub mask_poly_0: Option<sonic_pc::Commitment<E>>,
    /// Commitment to the `g_0` polynomials.
    pub g_0_commitments: Option<Vec<sonic_pc::Commitment<E>>>,
    /// Commitment to the `h_0` polynomial.
    pub h_0: sonic_pc::Commitment<E>,
    /// Commitment to the masking polynomial for lineval.
    pub mask_poly_1: Option<sonic_pc::Commitment<E>>,
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
        CanonicalSerialize::serialize_with_mode(&self.mask_poly_0, &mut writer, compress)?;
        // TODO: I can add an extra T: Vec impl for Option using serialize_vec_without_len
        CanonicalSerialize::serialize_with_mode(&self.g_0_commitments, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.h_0, &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.mask_poly_1, &mut writer, compress)?;
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
        size += CanonicalSerialize::serialized_size(&self.mask_poly_0, compress);
        // TODO: consider using serialized_opt_vec_size_without_len()
        size += CanonicalSerialize::serialized_size(&self.g_0_commitments, compress);
        size += CanonicalSerialize::serialized_size(&self.h_0, compress);
        size += CanonicalSerialize::serialized_size(&self.mask_poly_1, compress);
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
            mask_poly_0: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_0_commitments: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_0: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            mask_poly_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            h_1: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_commitments: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_b_commitments: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_c_commitments: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            h_2: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluations<F: PrimeField> {
    /// Evaluation of `g_1` at `beta`.
    pub g_1_eval: F,
    /// Evaluation of `g_a_i`'s at `beta`.
    pub g_a_evals: Vec<F>,
    /// Evaluation of `g_b_i`'s at `gamma`.
    pub g_b_evals: Vec<F>,
    /// Evaluation of `g_c_i`'s at `gamma`.
    pub g_c_evals: Vec<F>,
    // TODO: we should make lookup related evals Optional
    /// Evaluation of `s_mul` at `alpha`.
    pub s_mul_evals: Vec<F>,
    /// Evaluation of `s_lookup` at `alpha`.
    pub s_lookup_evals: Vec<F>,
    /// Evaluation of 'g_0_i_j's at `alpha`.
    pub g_0_evals: Vec<F>,
}

impl<F: PrimeField> Evaluations<F> {
    fn serialize_with_mode<W: snarkvm_utilities::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), snarkvm_utilities::SerializationError> {
        CanonicalSerialize::serialize_with_mode(&self.g_1_eval, &mut writer, compress)?;
        serialize_vec_without_len(self.g_a_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_b_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_c_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.s_mul_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.s_lookup_evals.iter(), &mut writer, compress)?;
        serialize_vec_without_len(self.g_0_evals.iter(), &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.g_1_eval, compress);
        size += serialized_vec_size_without_len(&self.g_a_evals, compress);
        size += serialized_vec_size_without_len(&self.g_b_evals, compress);
        size += serialized_vec_size_without_len(&self.g_c_evals, compress);
        size += serialized_vec_size_without_len(&self.s_mul_evals, compress);
        size += serialized_vec_size_without_len(&self.s_lookup_evals, compress);
        size += serialized_vec_size_without_len(&self.g_0_evals, compress);
        size
    }

    fn deserialize_with_mode<R: snarkvm_utilities::Read>(
        batch_sizes: &[usize],
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, snarkvm_utilities::SerializationError> {
        let total_instances = batch_sizes.iter().sum::<usize>();
        Ok(Evaluations {
            g_1_eval: CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?,
            g_a_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_b_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_c_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            s_mul_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            s_lookup_evals: deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?,
            g_0_evals: deserialize_vec_without_len(&mut reader, compress, validate, total_instances)?,
        })
    }
}

impl<F: PrimeField> Evaluations<F> {
    pub(crate) fn from_map(
        map: &std::collections::BTreeMap<String, F>,
        batch_sizes: BTreeMap<CircuitId, BatchSize>,
    ) -> Self {
        let mut g_a_evals = Vec::with_capacity(batch_sizes.len());
        let mut g_b_evals = Vec::with_capacity(batch_sizes.len());
        let mut g_c_evals = Vec::with_capacity(batch_sizes.len());
        let mut s_mul_evals = Vec::with_capacity(batch_sizes.len());
        let mut s_lookup_evals = Vec::with_capacity(batch_sizes.len());
        let mut g_0_evals = Vec::with_capacity(batch_sizes.len());

        for (label, value) in map {
            if label == "g_1" {
                break;
            }

            if label.contains("g_a") {
                g_a_evals.push(*value);
            } else if label.contains("g_b") {
                g_b_evals.push(*value);
            } else if label.contains("g_c") {
                g_c_evals.push(*value);
            } else if label.contains("s_mul") {
                s_mul_evals.push(*value);
            } else if label.contains("s_lookup") {
                s_lookup_evals.push(*value);
            } else if label.contains("g_0") {
                g_0_evals.push(*value);
            }
        }
        Self { g_1_eval: map["g_1"], g_a_evals, g_b_evals, g_c_evals, s_mul_evals, s_lookup_evals, g_0_evals }
    }

    pub(crate) fn get(&self, index: usize, label: &str) -> Option<F> {
        if label == "g_1" {
            return Some(self.g_1_eval);
        }

        if label.contains("g_a") {
            self.g_a_evals.get(index).copied()
        } else if label.contains("g_b") {
            self.g_b_evals.get(index).copied()
        } else if label.contains("g_c") {
            self.g_c_evals.get(index).copied()
        } else if label.contains("s_mul") {
            self.s_mul_evals.get(index).copied()
        } else if label.contains("s_lookup") {
            self.s_lookup_evals.get(index).copied()
        } else if label.contains("g_0") {
            self.g_0_evals.get(index).copied()
        } else {
            None
        }
    }

    pub fn to_field_elements(&self) -> Vec<F> {
        let mut result = vec![self.g_1_eval];
        result.extend_from_slice(&self.g_a_evals);
        result.extend_from_slice(&self.g_b_evals);
        result.extend_from_slice(&self.g_c_evals);
        result.extend_from_slice(&self.s_mul_evals);
        result.extend_from_slice(&self.s_lookup_evals);
        result.extend_from_slice(&self.g_0_evals);
        result
    }
}

impl<F: PrimeField> Valid for Evaluations<F> {
    fn check(&self) -> Result<(), snarkvm_utilities::SerializationError> {
        self.g_1_eval.check()?;
        self.g_a_evals.check()?;
        self.g_b_evals.check()?;
        self.g_c_evals.check()?;
        self.s_mul_evals.check()?;
        self.s_lookup_evals.check()?;
        self.g_0_evals.check()
    }
}

/// The size of a batch of instances to prove
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatchSize {
    /// The number of instances
    pub num_instances: usize, // TODO(vicsn) in PR#1499 this is changed to fixed size
    /// Whether these instances use lookups
    pub lookups_used: bool,
}

/// A zkSNARK proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E: PairingEngine> {
    /// The number of instances being proven in this proof, and whether they contain a lookup
    batch_sizes: Vec<BatchSize>,

    /// Commitments to prover polynomials.
    pub commitments: Commitments<E>,

    /// Evaluations of some of the committed polynomials.
    pub evaluations: Evaluations<E::Fr>,

    /// Prover message: sum_a, sum_b, sum_c for each instance
    pub third_msg: ThirdMessage<E::Fr>,

    /// Prover message: sum_a, sum_b, sum_c for each circuit
    pub fourth_msg: FourthMessage<E::Fr>,

    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: sonic_pc::BatchLCProof<E>,
}

impl<E: PairingEngine> Proof<E> {
    /// Construct a new proof.
    pub fn new(
        batch_sizes: BTreeMap<CircuitId, BatchSize>,
        commitments: Commitments<E>,
        evaluations: Evaluations<E::Fr>,
        third_msg: ThirdMessage<E::Fr>,
        fourth_msg: FourthMessage<E::Fr>,
        pc_proof: sonic_pc::BatchLCProof<E>,
    ) -> Result<Self, SNARKError> {
        let batch_sizes: Vec<BatchSize> = batch_sizes.into_values().collect();
        let total_instances = batch_sizes.iter().map(|b| b.num_instances).sum::<usize>();
        let lookup_instances = batch_sizes.iter().filter(|b| b.lookups_used).map(|b| b.num_instances).sum::<usize>();
        if commitments.witness_commitments.len() != total_instances {
            return Err(SNARKError::BatchSizeMismatch);
        }
        if let Some(g_0) = commitments.g_0_commitments.as_ref() {
            if g_0.len() != lookup_instances {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }
        Ok(Self { batch_sizes, commitments, evaluations, third_msg, fourth_msg, pc_proof })
    }

    pub fn batch_sizes(&self) -> Result<&[BatchSize], SNARKError> {
        let total_instances = self.batch_sizes.iter().map(|b| b.num_instances).sum::<usize>();
        let lookup_instances =
            self.batch_sizes.iter().filter(|b| b.lookups_used).map(|b| b.num_instances).sum::<usize>();
        if self.commitments.witness_commitments.len() != total_instances {
            return Err(SNARKError::BatchSizeMismatch);
        }
        if let Some(g_0) = self.commitments.g_0_commitments.as_ref() {
            if g_0.len() != lookup_instances {
                return Err(SNARKError::BatchSizeMismatch);
            }
        }
        Ok(&self.batch_sizes)
    }
}

impl<E: PairingEngine> CanonicalSerialize for Proof<E> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
        // TODO(vicsn) in PR#1499, batch_sizes.num_instances is changed to fixed size
        CanonicalSerialize::serialize_with_mode(&self.batch_sizes, &mut writer, compress)?;
        Commitments::serialize_with_mode(&self.commitments, &mut writer, compress)?;
        Evaluations::serialize_with_mode(&self.evaluations, &mut writer, compress)?;
        for third_sums in self.third_msg.sums.iter() {
            serialize_vec_without_len(third_sums.iter(), &mut writer, compress)?;
        }
        serialize_vec_without_len(self.fourth_msg.sums.iter(), &mut writer, compress)?;
        CanonicalSerialize::serialize_with_mode(&self.pc_proof, &mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, mode: Compress) -> usize {
        let mut size = 0;
        size += CanonicalSerialize::serialized_size(&self.batch_sizes, mode);
        size += Commitments::serialized_size(&self.commitments, mode);
        size += Evaluations::serialized_size(&self.evaluations, mode);
        for third_sums in self.third_msg.sums.iter() {
            size += serialized_vec_size_without_len(third_sums, mode);
        }
        size += serialized_vec_size_without_len(&self.fourth_msg.sums, mode);
        size += CanonicalSerialize::serialized_size(&self.pc_proof, mode);
        size
    }
}

impl<E: PairingEngine> Valid for Proof<E> {
    fn check(&self) -> Result<(), SerializationError> {
        self.batch_sizes.check()?;
        self.commitments.check()?;
        self.evaluations.check()?;
        self.third_msg.check()?;
        self.fourth_msg.check()?;
        self.pc_proof.check()
    }
}

impl<E: PairingEngine> CanonicalDeserialize for Proof<E> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let batch_sizes: Vec<BatchSize> = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let num_instances: Vec<usize> = batch_sizes.iter().map(|b| b.num_instances).collect();
        let commitments = Commitments::deserialize_with_mode(&num_instances, &mut reader, compress, validate)?;
        let evaluations = Evaluations::deserialize_with_mode(&num_instances, &mut reader, compress, validate)?;
        let third_msg_sums = num_instances
            .iter()
            .map(|&batch_size| deserialize_vec_without_len(&mut reader, compress, validate, batch_size))
            .collect::<Result<Vec<_>, _>>()?;
        let fourth_msg_sums = deserialize_vec_without_len(&mut reader, compress, validate, batch_sizes.len())?;
        Ok(Proof {
            commitments,
            evaluations,
            third_msg: ThirdMessage { sums: third_msg_sums },
            fourth_msg: FourthMessage { sums: fourth_msg_sums },
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
        snark::varuna::prover::MatrixSums,
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

    fn rand_commitments(j: usize, i: usize, test_with_none: bool) -> Commitments<Bls12_377> {
        assert!(i > 0);
        assert!(j > 0);
        let sample_commit = sample_commit();
        let mask_poly_0 = if test_with_none { None } else { Some(sample_commit) };
        let mask_poly_1 = if test_with_none { None } else { Some(sample_commit) };
        Commitments {
            witness_commitments: vec![
                WitnessCommitments { w: sample_commit, multiplicities: Some(sample_commit) };
                i * j
            ],
            mask_poly_0,
            g_0_commitments: Some(vec![sample_commit; j]),
            h_0: sample_commit,
            mask_poly_1,
            g_1: sample_commit,
            h_1: sample_commit,
            g_a_commitments: vec![sample_commit; i],
            g_b_commitments: vec![sample_commit; i],
            g_c_commitments: vec![sample_commit; i],
            h_2: sample_commit,
        }
    }

    fn rand_evaluations<F: PrimeField>(rng: &mut TestRng, i: usize, j: usize) -> Evaluations<F> {
        Evaluations {
            g_1_eval: F::rand(rng),
            g_a_evals: vec![F::rand(rng); i],
            g_b_evals: vec![F::rand(rng); i],
            g_c_evals: vec![F::rand(rng); i],
            s_mul_evals: vec![F::rand(rng); i],
            s_lookup_evals: vec![F::rand(rng); i],
            g_0_evals: vec![F::rand(rng); i * j],
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
                let commitments = rand_commitments(j, i, test_with_none);
                let batch_sizes = vec![j; i];
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
                println!("i: {}, j: {}", i, j);
                let evaluations: Evaluations<Fr> = rand_evaluations(rng, i, j);
                let batch_sizes = vec![j; i];
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
                let lookups_used = true;
                let batch_sizes = vec![BatchSize { num_instances: j, lookups_used }; i];
                let commitments = rand_commitments(j, i, test_with_none);
                let evaluations: Evaluations<Fr> = rand_evaluations(rng, i, j);
                let third_msg = ahp::prover::ThirdMessage::<Fr> { sums: vec![vec![rand_sums(rng); j]; i] };
                let fourth_msg = ahp::prover::FourthMessage::<Fr> { sums: vec![rand_sums(rng); i] };
                let mut proof_evaluations = None;
                if !test_with_none {
                    proof_evaluations = Some(vec![Fr::rand(rng); i]);
                }
                let pc_proof = sonic_pc::BatchLCProof {
                    proof: BatchProof(vec![rand_kzg_proof(rng, test_with_none); j]),
                    evaluations: proof_evaluations,
                };
                let proof = Proof { batch_sizes, commitments, evaluations, third_msg, fourth_msg, pc_proof };
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
