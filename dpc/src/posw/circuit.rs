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

//! Implements a Proof of Succinct work circuit. The inputs are opaque leaves,
//! which are then used to build a tree instantiated with a masked Pedersen hash. The prover
//! inputs a mask computed as Blake2s(nonce || root), which the verifier also checks.

use crate::Network;
use snarkvm_algorithms::{merkle_tree::MerkleTree, prelude::*};
use snarkvm_gadgets::{
    algorithms::merkle_tree::compute_root,
    integers::uint::UInt8,
    traits::{AllocGadget, CRHGadget, MaskedCRHGadget},
    EqGadget,
};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};
use snarkvm_utilities::ToBytes;

use anyhow::{anyhow, Result};
use blake2::{digest::Digest, Blake2s};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoSWCircuit<N: Network, const MASK_NUM_BYTES: usize> {
    hashed_leaves: Vec<<<N::PoswTreeParameters as MerkleParameters>::H as CRH>::Output>,
    mask: Vec<u8>,
    root: N::PoswRoot,
}

impl<N: Network, const MASK_NUM_BYTES: usize> PoSWCircuit<N, MASK_NUM_BYTES> {
    /// Creates a PoSW circuit from the provided transaction ids and nonce.
    pub fn new(nonce: u32, leaves: &[[u8; 32]]) -> Result<Self> {
        // Ensure the number of leaves is correct.
        if leaves.len() != N::POSW_NUM_LEAVES {
            return Err(anyhow!("PoSW number of leaves length is incorrect: {}", leaves.len()));
        }

        // Compute the Merkle root on hashed leaves.
        let tree = MerkleTree::<N::PoswTreeParameters>::new(Arc::new(N::posw_tree_parameters().clone()), leaves)?;
        let root = *tree.root();

        // Generate the mask by committing to the nonce and root.
        let mask = Self::commit(nonce, &root)?;

        Ok(Self {
            hashed_leaves: tree.hashed_leaves().to_vec(),
            mask,
            root,
        })
    }

    /// Creates a blank PoSW circuit for setup.
    pub fn blank() -> Result<Self> {
        let empty_hash = N::posw_tree_parameters()
            .hash_empty()
            .map_err(|_| SynthesisError::Unsatisfiable)?;

        Ok(Self {
            hashed_leaves: vec![empty_hash; N::POSW_NUM_LEAVES],
            mask: vec![0; MASK_NUM_BYTES],
            root: Default::default(),
        })
    }

    /// Returns a reference to the PoSW hashed leaves.
    pub fn hashed_leaves(&self) -> &Vec<<<N::PoswTreeParameters as MerkleParameters>::H as CRH>::Output> {
        &self.hashed_leaves
    }

    /// Returns a reference to the PoSW mask.
    pub fn mask(&self) -> &Vec<u8> {
        &self.mask
    }

    /// Returns a reference to the PoSW root.
    pub fn root(&self) -> &N::PoswRoot {
        &self.root
    }

    /// Commits to the given nonce and root.
    pub(super) fn commit(nonce: u32, root: &N::PoswRoot) -> Result<Vec<u8>> {
        let mut h = Blake2s::new();
        h.update(&nonce.to_le_bytes());
        h.update(&root.to_bytes_le()?);
        let mask = h.finalize().to_vec();

        match mask.len() == MASK_NUM_BYTES {
            true => Ok(mask),
            false => Err(anyhow!("PoSW mask length is incorrect: {}", mask.len())),
        }
    }
}

impl<N: Network, const MASK_NUM_BYTES: usize> ConstraintSynthesizer<N::InnerScalarField>
    for PoSWCircuit<N, MASK_NUM_BYTES>
{
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.hashed_leaves.len(), N::POSW_NUM_LEAVES);
        assert_eq!(self.mask.len(), MASK_NUM_BYTES);

        let crh_parameters = N::PoswTreeCRHGadget::alloc_constant(&mut cs.ns(|| "new_parameters"), || {
            Ok(N::posw_tree_parameters().crh().clone())
        })?;

        let mask_crh_parameters =
            <N::PoswTreeCRHGadget as MaskedCRHGadget<
                <N::PoswTreeParameters as MerkleParameters>::H,
                N::InnerScalarField,
            >>::MaskParametersGadget::alloc_constant(&mut cs.ns(|| "new_mask_parameters"), || {
                let crh_parameters = N::posw_tree_parameters().mask_crh();
                Ok(crh_parameters)
            })?;

        let mask_bytes = UInt8::alloc_input_vec_le(&mut cs.ns(|| "mask"), &self.mask)?;

        // Allocate the hashed leaves.
        let hashed_leaf_gadgets = self
            .hashed_leaves
            .iter()
            .enumerate()
            .map(|(i, leaf)| {
                <N::PoswTreeCRHGadget as CRHGadget<
                    <N::PoswTreeParameters as MerkleParameters>::H,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(cs.ns(|| format!("leaf {}", i)), || Ok(leaf))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Compute the root using the masked tree.
        let candidate_root =
            compute_root::<<N::PoswTreeParameters as MerkleParameters>::H, N::PoswTreeCRHGadget, _, _, _>(
                cs.ns(|| "compute masked root"),
                &crh_parameters,
                &mask_crh_parameters,
                &mask_bytes,
                &hashed_leaf_gadgets,
            )?;

        // Enforce the input root is the same as the computed root.
        let expected_root = <N::PoswTreeCRHGadget as CRHGadget<
            <N::PoswTreeParameters as MerkleParameters>::H,
            N::InnerScalarField,
        >>::OutputGadget::alloc_input(
            cs.ns(|| "alloc input expected masked root"), || Ok(&self.root)
        )?;
        candidate_root.enforce_equal(cs.ns(|| "enforce equal"), &expected_root)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{testnet1::Testnet1, testnet2::Testnet2};
    use snarkvm_fields::ToConstraintField;
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::FromBytes;

    use blake2::{digest::Digest, Blake2s};
    use rand::{rngs::ThreadRng, thread_rng, CryptoRng, Rng};
    use std::{sync::Arc, time::Instant};

    fn posw_public_inputs_test<N: Network>() {
        // Setup the given parameters.
        let nonce = 1u32;
        let leaves = vec![[3u8; 32]; N::POSW_NUM_LEAVES];

        // Generate the expected inputs.
        let (expected_hashed_leaves, expected_mask, expected_root) = {
            let tree =
                MerkleTree::<N::PoswTreeParameters>::new(Arc::new(N::posw_tree_parameters().clone()), &leaves[..])
                    .unwrap();
            let root = tree.root();

            let mut h = Blake2s::new();
            h.update(&nonce.to_le_bytes());
            h.update(root.to_bytes_le().unwrap());
            let mask = h.finalize().to_vec();

            let hashed_leaves = tree.hashed_leaves().to_vec();

            (hashed_leaves, mask, root.clone())
        };

        // Generate the candidate inputs.
        let candidate_circuit = PoSWCircuit::<N, 32>::new(nonce, &leaves).unwrap();
        assert_eq!(expected_hashed_leaves, candidate_circuit.hashed_leaves);
        assert_eq!(expected_mask, candidate_circuit.mask);
        assert_eq!(expected_root, candidate_circuit.root);
    }

    fn posw_constraints_test<N: Network>() {
        // Construct an assigned circuit.
        let nonce = 1u32;
        let leaves = vec![[3u8; 32]; N::POSW_NUM_LEAVES];
        let assigned_circuit = PoSWCircuit::<N, 32>::new(nonce, &leaves).unwrap();

        // Check that the constraint system was satisfied.
        let mut cs = TestConstraintSystem::<N::InnerScalarField>::new();
        assigned_circuit
            .generate_constraints(&mut cs.ns(|| "PoSW circuit"))
            .unwrap();

        if !cs.is_satisfied() {
            println!("Unsatisfied constraints:");
            println!("{}", cs.which_is_unsatisfied().unwrap());
        }

        let num_constraints = cs.num_constraints();
        println!("PoSW circuit num constraints: {:?}", num_constraints);
        assert_eq!(26663, num_constraints);
    }

    fn posw_proof_test<N: Network, R: Rng + CryptoRng>(rng: &mut R) {
        // Generate the proving and verifying key.
        let (proving_key, verifying_key) = {
            let max_degree =
                snarkvm_marlin::ahp::AHPForR1CS::<N::InnerScalarField>::max_degree(10000, 10000, 100000).unwrap();
            let universal_srs = <<N as Network>::PoswSNARK as SNARK>::universal_setup(&max_degree, rng).unwrap();

            <<N as Network>::PoswSNARK as SNARK>::setup::<_, R>(
                &PoSWCircuit::<N, 32>::blank().unwrap(),
                &mut SRS::<R, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Construct an assigned circuit.
        let nonce = 1u32;
        let leaves = vec![[3u8; 32]; N::POSW_NUM_LEAVES];
        let assigned_circuit = PoSWCircuit::<N, 32>::new(nonce, &leaves).unwrap();

        // Compute the proof.
        let proof = {
            let timer = Instant::now();
            let proof = <<N as Network>::PoswSNARK as SNARK>::prove(&proving_key, &assigned_circuit, rng).unwrap();
            println!("\nPosW elapsed time: {} ms\n", (Instant::now() - timer).as_millis());
            proof
        };
        assert_eq!(proof.to_bytes_le().unwrap().len(), N::POSW_PROOF_SIZE_IN_BYTES);

        // Verify the proof is valid on the public inputs.
        let inputs = [
            ToConstraintField::<<N as Network>::InnerScalarField>::to_field_elements(&assigned_circuit.mask[..])
                .unwrap(),
            vec![N::InnerScalarField::read_le(&assigned_circuit.root.to_bytes_le().unwrap()[..]).unwrap()],
        ]
        .concat();
        assert_eq!(3, inputs.len());
        assert!(<<N as Network>::PoswSNARK as SNARK>::verify(&verifying_key, &inputs, &proof).unwrap());
    }

    #[test]
    fn test_posw_public_inputs() {
        posw_public_inputs_test::<Testnet1>();
        posw_public_inputs_test::<Testnet2>();
    }

    #[test]
    fn test_posw_constraints() {
        posw_constraints_test::<Testnet1>();
        posw_constraints_test::<Testnet2>();
    }

    #[test]
    fn test_posw_proof() {
        posw_proof_test::<Testnet1, ThreadRng>(&mut thread_rng());
        posw_proof_test::<Testnet2, ThreadRng>(&mut thread_rng());
    }
}
