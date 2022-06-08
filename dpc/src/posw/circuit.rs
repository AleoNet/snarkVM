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

//! Implements a Proof of Succinct work circuit. The inputs are opaque leaves,
//! which are then used to build a tree instantiated with a masked Pedersen hash. The prover
//! inputs a mask computed as Blake2s(nonce || root), which the verifier also checks.

use crate::{BlockTemplate, Network};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::{
    algorithms::merkle_tree::compute_masked_root,
    traits::{AllocGadget, CRHGadget, MaskedCRHGadget, PRFGadget},
    EqGadget,
    ToBytesGadget,
};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use anyhow::Result;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoSWCircuit<N: Network> {
    block_header_root: N::BlockHeaderRoot,
    nonce: N::PoSWNonce,
    hashed_leaves: Vec<<<N::BlockHeaderRootParameters as MerkleParameters>::LeafCRH as CRH>::Output>,
}

impl<N: Network> PoSWCircuit<N> {
    /// Creates a PoSW circuit from the provided transaction ids and nonce.
    pub fn new(block_template: &BlockTemplate<N>, nonce: N::PoSWNonce) -> Result<Self> {
        let tree = block_template.to_header_tree()?;

        Ok(Self { block_header_root: (*tree.root()).into(), nonce, hashed_leaves: tree.hashed_leaves().to_vec() })
    }

    /// Creates a blank PoSW circuit for setup.
    pub fn blank() -> Result<Self> {
        let empty_hash = N::block_header_root_parameters().hash_empty().map_err(|_| SynthesisError::Unsatisfiable)?;

        Ok(Self {
            block_header_root: Default::default(),
            nonce: Default::default(),
            hashed_leaves: vec![empty_hash; usize::pow(2, N::HEADER_TREE_DEPTH as u32)],
        })
    }

    /// Returns the public inputs for the PoSW circuit.
    pub fn to_public_inputs(&self) -> Vec<N::InnerScalarField> {
        vec![*self.block_header_root, *self.nonce]
    }

    /// Returns the block nonce.
    pub fn nonce(&self) -> N::PoSWNonce {
        self.nonce
    }

    /// Sets the nonce to the given nonce.
    /// This method is used by PoSW to iterate over candidate block headers.
    pub(crate) fn set_nonce(&mut self, nonce: N::PoSWNonce) {
        self.nonce = nonce;
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for PoSWCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // Sanity check that the correct number of leaves are allocated.
        // Note: This is *not* enforced in the circuit.
        assert_eq!(usize::pow(2, N::HEADER_TREE_DEPTH as u32), self.hashed_leaves.len());

        let two_to_one_crh_parameters =
            N::BlockHeaderRootTwoToOneCRHGadget::alloc_constant(&mut cs.ns(|| "new_parameters"), || {
                Ok(N::block_header_root_parameters().two_to_one_crh())
            })?;

        let mask_crh_parameters = <N::BlockHeaderRootTwoToOneCRHGadget as MaskedCRHGadget<
            <N::BlockHeaderRootParameters as MerkleParameters>::TwoToOneCRH,
            N::InnerScalarField,
        >>::MaskParametersGadget::alloc_constant(
            &mut cs.ns(|| "new_mask_parameters"),
            || Ok(N::block_header_root_parameters().mask_crh()),
        )?;

        let block_header_root =
            <N::PoSWMaskPRFGadget as PRFGadget<N::PoSWMaskPRF, N::InnerScalarField>>::Seed::alloc_input(
                &mut cs.ns(|| "Declare block header root"),
                || Ok(self.block_header_root),
            )?;

        let nonce = <N::PoSWMaskPRFGadget as PRFGadget<N::PoSWMaskPRF, N::InnerScalarField>>::Input::alloc_input(
            &mut cs.ns(|| "Declare given nonce"),
            || Ok(vec![*self.nonce]),
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
                <N::BlockHeaderRootCRHGadget as CRHGadget<
                    <N::BlockHeaderRootParameters as MerkleParameters>::LeafCRH,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(cs.ns(|| format!("leaf {}", i)), || Ok(leaf))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Compute the root using the masked tree.
        let candidate_root = compute_masked_root::<
            <N::BlockHeaderRootParameters as MerkleParameters>::TwoToOneCRH,
            N::BlockHeaderRootTwoToOneCRHGadget,
            _,
            _,
            _,
        >(
            cs.ns(|| "compute masked root"),
            &two_to_one_crh_parameters,
            &mask_crh_parameters,
            &mask_bytes,
            &hashed_leaf_gadgets,
        )?;

        // Enforce the input root is the same as the computed root.
        candidate_root.enforce_equal(cs.ns(|| "enforce equal"), &block_header_root)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{testnet1::Testnet1, testnet2::Testnet2, PoSWProof};
    use snarkvm_algorithms::snark::marlin::{ahp::AHPForR1CS, MarlinHidingMode};
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::{FromBytes, ToBytes, Uniform};

    use rand::{rngs::ThreadRng, thread_rng, CryptoRng, Rng};
    use std::time::Instant;

    fn posw_constraints_test<N: Network>() {
        let mut cs = TestConstraintSystem::<N::InnerScalarField>::new();

        // Synthesize the PoSW circuit.
        PoSWCircuit::<N>::blank().unwrap().generate_constraints(&mut cs.ns(|| "PoSW circuit")).unwrap();

        // Check that the constraint system was satisfied.
        if !cs.is_satisfied() {
            println!("Unsatisfied constraints:");
            println!("{}", cs.which_is_unsatisfied().unwrap());
        }

        let num_constraints = cs.num_constraints();
        println!("PoSW circuit num constraints: {:?}", num_constraints);
        assert_eq!(26909, num_constraints);
    }

    fn posw_proof_test<N: Network, R: Rng + CryptoRng>(rng: &mut R) {
        // Generate the proving and verifying key.
        let (proving_key, verifying_key) = {
            let max_degree =
                AHPForR1CS::<N::InnerScalarField, MarlinHidingMode>::max_degree(20000, 20000, 200000).unwrap();
            let universal_srs = <<N as Network>::PoSWSNARK as SNARK>::universal_setup(&max_degree, rng).unwrap();

            <<N as Network>::PoSWSNARK as SNARK>::setup::<_, R>(
                &PoSWCircuit::<N>::blank().unwrap(),
                &mut SRS::<R, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Sample a random nonce.
        let nonce = Uniform::rand(rng);

        // Construct the block template.
        let block = N::genesis_block();
        let block_template = BlockTemplate::new(
            block.previous_block_hash(),
            block.height(),
            block.timestamp(),
            block.difficulty_target(),
            block.cumulative_weight(),
            block.previous_ledger_root(),
            block.transactions().clone(),
            block.to_coinbase_transaction().unwrap().to_records().next().unwrap(),
        );

        // Construct an assigned circuit.
        let assigned_circuit = PoSWCircuit::<N>::new(&block_template, nonce).unwrap();

        // Compute the proof.
        let proof = {
            let timer = Instant::now();
            let proof = <<N as Network>::PoSWSNARK as SNARK>::prove(&proving_key, &assigned_circuit, rng).unwrap();
            println!("\nPosW elapsed time: {} ms\n", (Instant::now() - timer).as_millis());
            proof
        };
        assert_eq!(
            PoSWProof::<N>::new(proof.clone().into()).to_bytes_le().unwrap().len(),
            N::HEADER_PROOF_SIZE_IN_BYTES
        );

        // Verify the proof is valid on the public inputs.
        let inputs = vec![
            N::InnerScalarField::read_le(&assigned_circuit.block_header_root.to_bytes_le().unwrap()[..]).unwrap(),
            *assigned_circuit.nonce,
        ];
        assert_eq!(2, inputs.len());
        assert!(<<N as Network>::PoSWSNARK as SNARK>::verify(&verifying_key, &inputs, &proof).unwrap());
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
