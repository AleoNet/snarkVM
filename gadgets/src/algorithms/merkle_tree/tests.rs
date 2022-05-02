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

use std::sync::Arc;

use blake2::{digest::Digest, Blake2s256};
use rand::{thread_rng, Rng};

use snarkvm_algorithms::{
    crh::{PedersenCRH, PedersenCompressedCRH, BHPCRH},
    merkle_tree::{MaskedMerkleTreeParameters, MerkleTree},
    traits::{MaskedMerkleParameters, MerkleParameters, CRH},
};
use snarkvm_curves::{
    bls12_377::Fr,
    edwards_bls12::{EdwardsAffine, EdwardsProjective},
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::ToBytes;

use crate::{
    algorithms::{
        crh::{BHPCRHGadget, PedersenCRHGadget, PedersenCompressedCRHGadget},
        merkle_tree::*,
    },
    curves::edwards_bls12::EdwardsBls12Gadget,
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, MaskedCRHGadget},
        alloc::AllocGadget,
        eq::EqGadget,
    },
};

const PEDERSEN_NUM_WINDOWS: usize = 256;
const PEDERSEN_WINDOW_SIZE: usize = 4;
const PEDERSEN_LEAF_WINDOW_SIZE: usize = 2;

const BHP_NUM_WINDOWS: usize = 32;
const BHP_WINDOW_SIZE: usize = 60;
const BHP_LEAF_WINDOW_SIZE: usize = 30;

fn generate_merkle_tree<
    P: MerkleParameters,
    F: PrimeField,
    LeafCRHGadget: CRHGadget<P::LeafCRH, F, OutputGadget = TwoToOneCRHGadget::OutputGadget>,
    TwoToOneCRHGadget: CRHGadget<P::TwoToOneCRH, F>,
>(
    leaves: &[[u8; 30]],
    use_bad_root: bool,
) {
    let parameters = P::setup("merkle_tree_test");
    let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
    let root = tree.root();
    let mut satisfied = true;
    for (i, leaf) in leaves.iter().enumerate() {
        let mut cs = TestConstraintSystem::<F>::new();
        let proof = tree.generate_proof(i, &leaf).unwrap();
        assert!(proof.verify(root, &leaf).unwrap());

        // Allocate Merkle tree root
        let root = <TwoToOneCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc(
            &mut cs.ns(|| format!("new_digest_{}", i)),
            || {
                if use_bad_root { Ok(<P::TwoToOneCRH as CRH>::Output::default()) } else { Ok(*root) }
            },
        )
        .unwrap();

        let constraints_from_digest = cs.num_constraints();
        println!("constraints from digest: {}", constraints_from_digest);

        // Allocate CRH
        let leaf_crh_parameters =
            LeafCRHGadget::alloc_constant(&mut cs.ns(|| format!("new_leaf_parameters_{}", i)), || {
                Ok(parameters.leaf_crh().clone())
            })
            .unwrap();
        let two_to_one_crh_parameters =
            TwoToOneCRHGadget::alloc_constant(&mut cs.ns(|| format!("new_two_to_one_parameters_{}", i)), || {
                Ok(parameters.two_to_one_crh().clone())
            })
            .unwrap();

        let constraints_from_parameters = cs.num_constraints() - constraints_from_digest;
        println!("constraints from parameters: {}", constraints_from_parameters);

        // Allocate Leaf
        let leaf_g = UInt8::constant_vec(leaf);

        let constraints_from_leaf = cs.num_constraints() - constraints_from_parameters - constraints_from_digest;
        println!("constraints from leaf: {}", constraints_from_leaf);

        // Allocate Merkle tree path
        let cw = MerklePathGadget::<_, LeafCRHGadget, TwoToOneCRHGadget, _>::alloc(
            &mut cs.ns(|| format!("new_witness_{}", i)),
            || Ok(proof),
        )
        .unwrap();

        let constraints_from_path =
            cs.num_constraints() - constraints_from_parameters - constraints_from_digest - constraints_from_leaf;
        println!("constraints from path: {}", constraints_from_path);
        let leaf_g: &[UInt8] = leaf_g.as_slice();
        cw.check_membership(
            &mut cs.ns(|| format!("new_witness_check_{}", i)),
            &leaf_crh_parameters,
            &two_to_one_crh_parameters,
            &root,
            &leaf_g,
        )
        .unwrap();
        if !cs.is_satisfied() {
            satisfied = false;
            println!("Unsatisfied constraint: {}", cs.which_is_unsatisfied().unwrap());
        }
        let setup_constraints =
            constraints_from_leaf + constraints_from_digest + constraints_from_parameters + constraints_from_path;
        println!("number of constraints: {}", cs.num_constraints() - setup_constraints);
    }

    assert!(satisfied);
}

fn generate_masked_merkle_tree<
    P: MaskedMerkleParameters,
    F: PrimeField,
    LeafCRHGadget: CRHGadget<P::LeafCRH, F, OutputGadget = TwoToOneCRHGadget::OutputGadget>,
    TwoToOneCRHGadget: MaskedCRHGadget<P::TwoToOneCRH, F>,
>(
    leaves: &[[u8; 30]],
    use_bad_root: bool,
) {
    let parameters = P::setup("merkle_tree_test");
    let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
    let root = tree.root();

    let mut cs = TestConstraintSystem::<F>::new();
    let leaf_gadgets = tree
        .hashed_leaves()
        .iter()
        .enumerate()
        .map(|(i, l)| {
            <LeafCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc(cs.ns(|| format!("leaf {}", i)), || Ok(l))
        })
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    let nonce: [u8; 4] = rand::random();
    let mut root_bytes = [0u8; 32];
    root.write_le(&mut root_bytes[..]).unwrap();

    let mut h = Blake2s256::new();
    h.update(nonce.as_ref());
    h.update(&root_bytes);
    let mask = h.finalize().to_vec();
    let mask_bytes = UInt8::alloc_vec(cs.ns(|| "mask"), &mask).unwrap();

    let two_to_one_crh_parameters =
        TwoToOneCRHGadget::alloc_constant(&mut cs.ns(|| "new_two_to_oneparameters"), || {
            Ok(parameters.two_to_one_crh().clone())
        })
        .unwrap();

    let mask_crh_parameters = <TwoToOneCRHGadget as MaskedCRHGadget<_, _>>::MaskParametersGadget::alloc_constant(
        &mut cs.ns(|| "new_mask_parameters"),
        || Ok(parameters.mask_crh().clone()),
    )
    .unwrap();

    let computed_root = compute_masked_root::<_, TwoToOneCRHGadget, _, _, _>(
        cs.ns(|| "compute masked root"),
        &two_to_one_crh_parameters,
        &mask_crh_parameters,
        &mask_bytes,
        &leaf_gadgets,
    )
    .unwrap();

    let given_root = if use_bad_root { <P::LeafCRH as CRH>::Output::default() } else { *root };

    let given_root_gadget =
        <TwoToOneCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc(&mut cs.ns(|| "given root"), || Ok(given_root))
            .unwrap();

    computed_root
        .enforce_equal(&mut cs.ns(|| "Check that computed root matches provided root"), &given_root_gadget)
        .unwrap();

    if !cs.is_satisfied() {
        println!("Unsatisfied constraint: {}", cs.which_is_unsatisfied().unwrap());
    }
    assert!(cs.is_satisfied());
}

fn update_merkle_tree<
    P: MerkleParameters,
    F: PrimeField,
    LeafCRHGadget: CRHGadget<P::LeafCRH, F, OutputGadget = TwoToOneCRHGadget::OutputGadget>,
    TwoToOneCRHGadget: CRHGadget<P::TwoToOneCRH, F>,
>(
    leaves: &[[u8; 30]],
) {
    let merkle_parameters = Arc::new(P::setup("merkle_tree_test"));
    let tree = MerkleTree::<P>::new(merkle_parameters.clone(), leaves).unwrap();
    let root = tree.root();

    let mut satisfied = true;
    for (i, leaf) in leaves.iter().enumerate() {
        let proof = tree.generate_proof(i, &leaf).unwrap();
        assert!(proof.verify(root, &leaf).unwrap());

        let mut updated_leaves = leaves.to_vec();
        updated_leaves[i] = [u8::MAX; 30];

        let new_tree = MerkleTree::<P>::new(merkle_parameters.clone(), &updated_leaves[..]).unwrap();
        let new_proof = new_tree.generate_proof(i, &updated_leaves[i]).unwrap();
        let new_root = new_tree.root();

        assert!(new_proof.verify(new_root, &updated_leaves[i]).unwrap());

        let mut cs = TestConstraintSystem::<F>::new();

        let leaf_crh =
            LeafCRHGadget::alloc_constant(&mut cs.ns(|| "leaf_crh"), || Ok(merkle_parameters.leaf_crh())).unwrap();
        let two_to_one_crh = TwoToOneCRHGadget::alloc_constant(&mut cs.ns(|| "two_to_one_crh"), || {
            Ok(merkle_parameters.two_to_one_crh())
        })
        .unwrap();

        // Allocate Merkle tree root
        let root =
            <TwoToOneCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc(&mut cs.ns(|| "root"), || Ok(root)).unwrap();

        // Allocate new Merkle tree root
        let new_root =
            <TwoToOneCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc(&mut cs.ns(|| "new_root"), || Ok(new_root))
                .unwrap();

        let path =
            MerklePathGadget::<_, LeafCRHGadget, TwoToOneCRHGadget, _>::alloc(&mut cs.ns(|| "path"), || Ok(proof))
                .unwrap();

        let leaf_gadget = UInt8::alloc_vec(cs.ns(|| "alloc_leaf"), &leaves[i]).unwrap();
        let new_leaf_gadget = UInt8::alloc_vec(cs.ns(|| "alloc_new_leaf"), &updated_leaves[i]).unwrap();

        path.update_and_check(
            cs.ns(|| "update_and_check"),
            &leaf_crh,
            &two_to_one_crh,
            &root,
            &new_root,
            &leaf_gadget,
            &new_leaf_gadget,
        )
        .unwrap();

        if !cs.is_satisfied() {
            satisfied = false;
            println!("Unsatisfied constraint: {}", cs.which_is_unsatisfied().unwrap());
        }
    }

    assert!(satisfied);
}

mod merkle_tree_pedersen_crh {
    use super::*;

    type LeafCRH = PedersenCRH<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
    type TwoToOneCRH = PedersenCRH<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_WINDOW_SIZE>;
    type LeafCRHGadget =
        PedersenCRHGadget<EdwardsAffine, Fr, EdwardsBls12Gadget, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
    type TwoToOneCRHGadget =
        PedersenCRHGadget<EdwardsAffine, Fr, EdwardsBls12Gadget, PEDERSEN_NUM_WINDOWS, PEDERSEN_WINDOW_SIZE>;

    type EdwardsMerkleParameters = MaskedMerkleTreeParameters<LeafCRH, TwoToOneCRH, 4>;

    #[test]
    fn good_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, false);
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, true);
    }

    #[test]
    fn update_merkle_tree_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        update_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves);
    }
}

mod merkle_tree_compressed_pedersen_crh {
    use super::*;

    type LeafCRH = PedersenCompressedCRH<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
    type TwoToOneCRH = PedersenCompressedCRH<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_WINDOW_SIZE>;
    type LeafCRHGadget = PedersenCompressedCRHGadget<
        EdwardsAffine,
        Fr,
        EdwardsBls12Gadget,
        PEDERSEN_NUM_WINDOWS,
        PEDERSEN_LEAF_WINDOW_SIZE,
    >;
    type TwoToOneCRHGadget =
        PedersenCompressedCRHGadget<EdwardsAffine, Fr, EdwardsBls12Gadget, PEDERSEN_NUM_WINDOWS, PEDERSEN_WINDOW_SIZE>;

    type EdwardsMerkleParameters = MaskedMerkleTreeParameters<LeafCRH, TwoToOneCRH, 4>;

    #[test]
    fn good_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, false);
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, true);
    }

    #[test]
    fn good_masked_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_masked_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, false);
    }

    #[should_panic]
    #[test]
    fn bad_masked_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_masked_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, true);
    }

    #[test]
    fn update_merkle_tree_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        update_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves);
    }
}

mod merkle_tree_bowe_hopwood_pedersen_crh {
    use super::*;

    type LeafCRH = BHPCRH<EdwardsProjective, BHP_NUM_WINDOWS, BHP_LEAF_WINDOW_SIZE>;
    type TwoToOneCRH = BHPCRH<EdwardsProjective, BHP_NUM_WINDOWS, BHP_WINDOW_SIZE>;
    type LeafCRHGadget = BHPCRHGadget<EdwardsAffine, Fr, EdwardsBls12Gadget, BHP_NUM_WINDOWS, BHP_LEAF_WINDOW_SIZE>;
    type TwoToOneCRHGadget = BHPCRHGadget<EdwardsAffine, Fr, EdwardsBls12Gadget, BHP_NUM_WINDOWS, BHP_WINDOW_SIZE>;

    type EdwardsMerkleParameters = MaskedMerkleTreeParameters<LeafCRH, TwoToOneCRH, 4>;

    #[test]
    fn good_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, false);
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, true);
    }

    #[test]
    fn update_merkle_tree_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        update_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves);
    }
}

mod merkle_tree_poseidon {
    use super::*;
    use crate::algorithms::crh::PoseidonCRHGadget;
    use snarkvm_algorithms::crh::PoseidonCRH;

    type LeafCRH = PoseidonCRH<Fr, 2>;
    type TwoToOneCRH = PoseidonCRH<Fr, 3>;
    type LeafCRHGadget = PoseidonCRHGadget<Fr, 2>;
    type TwoToOneCRHGadget = PoseidonCRHGadget<Fr, 3>;

    type EdwardsMerkleParameters = MaskedMerkleTreeParameters<LeafCRH, TwoToOneCRH, 4>;

    #[test]
    fn good_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, false);
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        generate_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves, true);
    }

    #[test]
    fn update_merkle_tree_test() {
        let mut rng = thread_rng();
        let mut leaves = Vec::new();

        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            let mut input = [0u8; 30];
            rng.fill(&mut input);
            leaves.push(input);
        }
        update_merkle_tree::<EdwardsMerkleParameters, Fr, LeafCRHGadget, TwoToOneCRHGadget>(&leaves);
    }
}
