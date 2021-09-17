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

use crate::{posw::posw::commit, MaskedMerkleRoot, Network};
use snarkvm_algorithms::{merkle_tree::MerkleTree, MaskedMerkleParameters, MerkleParameters, CRH};
use snarkvm_gadgets::{
    algorithms::merkle_tree::compute_root,
    integers::uint::UInt8,
    traits::{AllocGadget, CRHGadget, MaskedCRHGadget},
    EqGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, Assignment, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::ToBytes;

use anyhow::Result;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct POSWCircuit<N: Network, const MASK_NUM_BYTES: usize> {
    pub hashed_leaves: Vec<Option<<<N::MaskedMerkleTreeParameters as MerkleParameters>::H as CRH>::Output>>,
    pub mask: Option<Vec<u8>>,
    pub root: Option<<<N::MaskedMerkleTreeParameters as MerkleParameters>::H as CRH>::Output>,
}

impl<N: Network, const MASK_NUM_BYTES: usize> POSWCircuit<N, MASK_NUM_BYTES> {
    /// Creates a POSW circuit from the provided transaction ids and nonce.
    pub fn new(nonce: u32, leaves: &[[u8; 32]]) -> Result<Self> {
        let tree = MerkleTree::<N::MaskedMerkleTreeParameters>::new(
            Arc::new(N::masked_merkle_tree_parameters().clone()),
            leaves,
        )?;
        let root = tree.root();

        // Generate the mask by committing to the nonce and root.
        let mask = commit(nonce, &MaskedMerkleRoot::new(&root.to_bytes_le()?));

        // Convert the leaves to Options for the SNARK
        let hashed_leaves = tree.hashed_leaves().into_iter().cloned().map(Some).collect();

        Ok(Self {
            hashed_leaves,
            mask: Some(mask),
            root: Some(*root),
        })
    }
}

impl<N: Network, const MASK_NUM_BYTES: usize> ConstraintSynthesizer<N::InnerScalarField>
    for POSWCircuit<N, MASK_NUM_BYTES>
{
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let cs = &mut cs.ns(|| "PoSW circuit");

        // Compute the mask if it exists.
        let mask = self.mask.clone().unwrap_or_else(|| vec![0; MASK_NUM_BYTES]);
        if mask.len() != MASK_NUM_BYTES {
            return Err(SynthesisError::Unsatisfiable);
        }
        let mask_bytes = UInt8::alloc_input_vec_le(&mut cs.ns(|| "mask"), &mask)?;

        let crh_parameters = N::MaskedMerkleTreeCRHGadget::alloc_constant(&mut cs.ns(|| "new_parameters"), || {
            Ok(N::masked_merkle_tree_parameters().crh().clone())
        })?;
        let mask_crh_parameters =
            <N::MaskedMerkleTreeCRHGadget as MaskedCRHGadget<
                <N::MaskedMerkleTreeParameters as MerkleParameters>::H,
                N::InnerScalarField,
            >>::MaskParametersGadget::alloc_constant(&mut cs.ns(|| "new_mask_parameters"), || {
                let crh_parameters = N::masked_merkle_tree_parameters().mask_crh();
                Ok(crh_parameters)
            })?;
        let leaves_number = 2u32.pow(<N::MaskedMerkleTreeParameters as MerkleParameters>::DEPTH as u32) as usize;
        assert!(self.hashed_leaves.len() <= leaves_number);

        // Initialize the leaves.
        let mut leaf_gadgets = self
            .hashed_leaves
            .iter()
            .enumerate()
            .map(|(i, l)| {
                <N::MaskedMerkleTreeCRHGadget as CRHGadget<
                    <N::MaskedMerkleTreeParameters as MerkleParameters>::H,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(cs.ns(|| format!("leaf {}", i)), || l.as_ref().get())
            })
            .collect::<Result<Vec<_>, _>>()?;

        let empty_hash = N::masked_merkle_tree_parameters()
            .hash_empty()
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        for i in leaf_gadgets.len()..leaves_number {
            leaf_gadgets.push(<N::MaskedMerkleTreeCRHGadget as CRHGadget<
                <N::MaskedMerkleTreeParameters as MerkleParameters>::H,
                N::InnerScalarField,
            >>::OutputGadget::alloc(
                cs.ns(|| format!("leaf {}", i)), || Ok(empty_hash.clone())
            )?);
        }

        // Compute the root using the masked tree.
        let computed_root = compute_root::<
            <N::MaskedMerkleTreeParameters as MerkleParameters>::H,
            N::MaskedMerkleTreeCRHGadget,
            _,
            _,
            _,
        >(
            cs.ns(|| "compute masked root"),
            &crh_parameters,
            &mask_crh_parameters,
            &mask_bytes,
            &leaf_gadgets,
        )?;

        // Enforce the input root is the same as the computed root.
        let public_computed_root =
            <N::MaskedMerkleTreeCRHGadget as CRHGadget<
                <N::MaskedMerkleTreeParameters as MerkleParameters>::H,
                N::InnerScalarField,
            >>::OutputGadget::alloc_input(cs.ns(|| "public computed root"), || self.root.as_ref().get())?;
        computed_root.enforce_equal(cs.ns(|| "inputize computed root"), &public_computed_root)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::testnet2::Testnet2;
    // TODO (howardwu) - Switch this to Marlin.
    use snarkvm_algorithms::snark::gm17::{
        create_random_proof,
        generate_random_parameters,
        prepare_verifying_key,
        verify_proof,
    };
    use snarkvm_curves::bls12_377::Bls12_377;
    use snarkvm_fields::ToConstraintField;

    use blake2::{digest::Digest, Blake2s};
    use rand::thread_rng;
    use std::sync::Arc;

    #[test]
    fn test_tree_proof() {
        let mut rng = thread_rng();

        let params = generate_random_parameters::<Bls12_377, _, _>(
            &POSWCircuit::<Testnet2, 32> {
                hashed_leaves: vec![None; 4],
                mask: None,
                root: None,
            },
            &mut rng,
        )
        .unwrap();

        let nonce = [1; 32];
        let leaves = vec![vec![3u8; 32]; 4];
        let tree = MerkleTree::new(Arc::new(Testnet2::masked_merkle_tree_parameters().clone()), &leaves[..]).unwrap();
        let root = tree.root();
        let mut root_bytes = [0; 32];
        root.write_le(&mut root_bytes[..]).unwrap();

        let mut h = Blake2s::new();
        h.update(nonce.as_ref());
        h.update(root_bytes.as_ref());
        let mask = h.finalize().to_vec();

        let snark_leaves = tree.hashed_leaves().to_vec().into_iter().map(Some).collect();
        let proof = create_random_proof(
            &POSWCircuit::<Testnet2, 32> {
                hashed_leaves: snark_leaves,
                mask: Some(mask.clone()),
                root: Some(root.clone()),
            },
            &params,
            &mut rng,
        )
        .unwrap();

        let inputs = [
            ToConstraintField::<<Testnet2 as Network>::InnerScalarField>::to_field_elements(&mask[..]).unwrap(),
            vec![root.clone()],
        ]
        .concat();

        assert!(verify_proof(&prepare_verifying_key(params.vk), &proof, &inputs,).unwrap());
    }
}
