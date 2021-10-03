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

use crate::{BlockHeader, Network};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::{
    algorithms::merkle_tree::compute_root,
    traits::{AllocGadget, CRHGadget, MaskedCRHGadget, PRFGadget},
    EqGadget,
    ToBytesGadget,
};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use anyhow::Result;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoSWCircuit<N: Network> {
    block_header_root: N::BlockHeaderRoot,
    nonce: N::InnerScalarField,
    hashed_leaves: Vec<<<N::BlockHeaderTreeParameters as MerkleParameters>::H as CRH>::Output>,
}

impl<N: Network> PoSWCircuit<N> {
    /// Creates a PoSW circuit from the provided transaction ids and nonce.
    pub fn new(block_header: &BlockHeader<N>) -> Result<Self> {
        let tree = block_header.to_header_tree()?;

        Ok(Self {
            block_header_root: *tree.root(),
            nonce: block_header.nonce(),
            hashed_leaves: tree.hashed_leaves().to_vec(),
        })
    }

    /// Creates a blank PoSW circuit for setup.
    pub fn blank() -> Result<Self> {
        let empty_hash = N::block_header_tree_parameters()
            .hash_empty()
            .map_err(|_| SynthesisError::Unsatisfiable)?;

        Ok(Self {
            block_header_root: Default::default(),
            nonce: Default::default(),
            hashed_leaves: vec![empty_hash; N::POSW_NUM_LEAVES],
        })
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for PoSWCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.hashed_leaves.len(), N::POSW_NUM_LEAVES);

        let crh_parameters = N::BlockHeaderTreeCRHGadget::alloc_constant(&mut cs.ns(|| "new_parameters"), || {
            Ok(N::block_header_tree_parameters().crh().clone())
        })?;

        let mask_crh_parameters =
            <N::BlockHeaderTreeCRHGadget as MaskedCRHGadget<
                <N::BlockHeaderTreeParameters as MerkleParameters>::H,
                N::InnerScalarField,
            >>::MaskParametersGadget::alloc_constant(&mut cs.ns(|| "new_mask_parameters"), || {
                let crh_parameters = N::block_header_tree_parameters().mask_crh();
                Ok(crh_parameters)
            })?;

        let block_header_root =
            <N::PoSWMaskPRFGadget as PRFGadget<N::PoSWMaskPRF, N::InnerScalarField>>::Seed::alloc_input(
                &mut cs.ns(|| "Declare block header root"),
                || Ok(self.block_header_root),
            )?;

        let nonce = <N::PoSWMaskPRFGadget as PRFGadget<N::PoSWMaskPRF, N::InnerScalarField>>::Input::alloc_input(
            &mut cs.ns(|| "Declare given nonce"),
            || Ok(vec![self.nonce]),
        )?;

        let mask = <N::PoSWMaskPRFGadget as PRFGadget<N::PoSWMaskPRF, N::InnerScalarField>>::check_evaluation_gadget(
            &mut cs.ns(|| "Compute mask"),
            &block_header_root,
            &nonce,
        )?;

        let mask_bytes = mask.to_bytes(&mut cs.ns(|| "mask to bytes"))?;

        // Allocate the hashed leaves.
        let hashed_leaf_gadgets = self
            .hashed_leaves
            .iter()
            .enumerate()
            .map(|(i, leaf)| {
                <N::BlockHeaderTreeCRHGadget as CRHGadget<
                    <N::BlockHeaderTreeParameters as MerkleParameters>::H,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(cs.ns(|| format!("leaf {}", i)), || Ok(leaf))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Compute the root using the masked tree.
        let candidate_root = compute_root::<
            <N::BlockHeaderTreeParameters as MerkleParameters>::H,
            N::BlockHeaderTreeCRHGadget,
            _,
            _,
            _,
        >(
            cs.ns(|| "compute masked root"),
            &crh_parameters,
            &mask_crh_parameters,
            &mask_bytes,
            &hashed_leaf_gadgets,
        )?;

        // Enforce the input root is the same as the computed root.
        let expected_root = <N::BlockHeaderTreeCRHGadget as CRHGadget<
            <N::BlockHeaderTreeParameters as MerkleParameters>::H,
            N::InnerScalarField,
        >>::OutputGadget::alloc_input(
            cs.ns(|| "alloc input expected block header root"),
            || Ok(&self.block_header_root),
        )?;
        candidate_root.enforce_equal(cs.ns(|| "enforce equal"), &expected_root)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{testnet1::Testnet1, testnet2::Testnet2};
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::{FromBytes, ToBytes};

    use rand::{rngs::ThreadRng, thread_rng, CryptoRng, Rng};
    use std::time::Instant;

    fn posw_constraints_test<N: Network>() {
        let mut cs = TestConstraintSystem::<N::InnerScalarField>::new();

        // Synthesize the PoSW circuit.
        PoSWCircuit::<N>::blank()
            .unwrap()
            .generate_constraints(&mut cs.ns(|| "PoSW circuit"))
            .unwrap();

        // Check that the constraint system was satisfied.
        if !cs.is_satisfied() {
            println!("Unsatisfied constraints:");
            println!("{}", cs.which_is_unsatisfied().unwrap());
        }

        let num_constraints = cs.num_constraints();
        println!("PoSW circuit num constraints: {:?}", num_constraints);
        assert_eq!(61535, num_constraints);
    }

    fn posw_proof_test<N: Network, R: Rng + CryptoRng>(rng: &mut R) {
        // Generate the proving and verifying key.
        let (proving_key, verifying_key) = {
            let max_degree =
                snarkvm_marlin::ahp::AHPForR1CS::<N::InnerScalarField>::max_degree(20000, 20000, 200000).unwrap();
            let universal_srs = <<N as Network>::PoswSNARK as SNARK>::universal_setup(&max_degree, rng).unwrap();

            <<N as Network>::PoswSNARK as SNARK>::setup::<_, R>(
                &PoSWCircuit::<N>::blank().unwrap(),
                &mut SRS::<R, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Construct an assigned circuit.
        let assigned_circuit = PoSWCircuit::<N>::new(N::genesis_block().header()).unwrap();

        // Compute the proof.
        let proof = {
            let timer = Instant::now();
            let proof = <<N as Network>::PoswSNARK as SNARK>::prove(&proving_key, &assigned_circuit, rng).unwrap();
            println!("\nPosW elapsed time: {} ms\n", (Instant::now() - timer).as_millis());
            proof
        };
        assert_eq!(proof.to_bytes_le().unwrap().len(), N::POSW_PROOF_SIZE_IN_BYTES);

        // Verify the proof is valid on the public inputs.
        let inputs = [vec![assigned_circuit.nonce], vec![
            N::InnerScalarField::read_le(&assigned_circuit.block_header_root.to_bytes_le().unwrap()[..]).unwrap(),
        ]]
        .concat();
        assert_eq!(2, inputs.len());
        assert!(<<N as Network>::PoswSNARK as SNARK>::verify(&verifying_key, &inputs, &proof).unwrap());
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
