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

use crate::{
    crh::{PedersenCRH, PedersenCompressedCRH},
    merkle_tree::{MerklePath, MerkleTree, MerkleTreeParameters},
    traits::{MerkleParameters, CRH},
};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use rand::{thread_rng, Rng};

use std::sync::Arc;

/// Generates the specified number of random Merkle tree leaves.
macro_rules! generate_random_leaves {
    ($num_leaves:expr, $leaf_size:expr) => {{
        let mut rng = thread_rng();

        let mut vec = Vec::with_capacity($num_leaves);
        for _ in 0..$num_leaves {
            let mut id = [0u8; $leaf_size];
            rng.fill(&mut id);
            vec.push(id);
        }
        vec
    }};
}

/// Generates a valid Merkle tree and verifies the Merkle path witness for each leaf.
fn generate_merkle_tree<P: MerkleParameters, L: ToBytes + Send + Sync + Clone + Eq>(
    leaves: &[L],
    parameters: &P,
) -> MerkleTree<P> {
    let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
    for (i, leaf) in leaves.iter().enumerate() {
        let proof = tree.generate_proof(i, &leaf).unwrap();
        assert_eq!(P::DEPTH, proof.path.len());
        assert!(proof.verify(tree.root(), &leaf).unwrap());
    }
    tree
}

/// Generates a valid Merkle tree and verifies the Merkle path witness for each leaf does not verify to an invalid root hash.
fn bad_merkle_tree_verify<P: MerkleParameters, L: ToBytes + Send + Sync + Clone + Eq>(leaves: &[L], parameters: &P) {
    let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
    for (i, leaf) in leaves.iter().enumerate() {
        let proof = tree.generate_proof(i, &leaf).unwrap();
        assert!(proof.verify(&<P::LeafCRH as CRH>::Output::default(), &leaf).unwrap());
    }
}

fn run_empty_merkle_tree_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");
    generate_merkle_tree::<P, Vec<u8>>(&[], parameters);
}

fn run_good_root_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");

    let leaves = generate_random_leaves!(4, 8);
    generate_merkle_tree::<P, _>(&leaves, parameters);

    let leaves = generate_random_leaves!(15, 8);
    generate_merkle_tree::<P, _>(&leaves, parameters);
}

fn run_bad_root_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");

    let leaves = generate_random_leaves!(4, 8);
    generate_merkle_tree::<P, _>(&leaves, parameters);

    let leaves = generate_random_leaves!(15, 8);
    bad_merkle_tree_verify::<P, _>(&leaves, parameters);
}

fn depth_2_merkle_tree_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");
    let leaf_crh = parameters.leaf_crh();
    let two_to_one_crh = parameters.two_to_one_crh();

    // Evaluate the Merkle tree root.
    let leaves = generate_random_leaves!(4, 64);
    let merkle_tree = generate_merkle_tree(&leaves, parameters);
    let merkle_tree_root = merkle_tree.root();

    // Evaluate the root by direct hashing.
    let expected_root = {
        // depth 2
        let leaf1 = leaf_crh.hash_bytes(&leaves[0]).unwrap();
        let leaf2 = leaf_crh.hash_bytes(&leaves[1]).unwrap();
        let leaf3 = leaf_crh.hash_bytes(&leaves[2]).unwrap();
        let leaf4 = leaf_crh.hash_bytes(&leaves[3]).unwrap();

        // depth 1
        let left = two_to_one_crh.hash_bytes(&to_bytes_le![leaf1, leaf2].unwrap()).unwrap();
        let right = two_to_one_crh.hash_bytes(&to_bytes_le![leaf3, leaf4].unwrap()).unwrap();

        // depth 0
        two_to_one_crh.hash_bytes(&to_bytes_le![left, right].unwrap()).unwrap()
    };

    println!("{} == {}", merkle_tree_root, &expected_root);
    assert_eq!(merkle_tree_root, &expected_root);
}

fn padded_merkle_tree_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");
    let leaf_crh = parameters.leaf_crh();
    let two_to_one_crh = parameters.two_to_one_crh();

    // Evaluate the Merkle tree root

    let leaves = generate_random_leaves!(4, 64);
    let merkle_tree = generate_merkle_tree(&leaves, parameters);
    let merkle_tree_root = merkle_tree.root();

    // Evaluate the root by direct hashing.
    let expected_root = {
        // depth 3
        let leaf1 = leaf_crh.hash_bytes(&leaves[0]).unwrap();
        let leaf2 = leaf_crh.hash_bytes(&leaves[1]).unwrap();
        let leaf3 = leaf_crh.hash_bytes(&leaves[2]).unwrap();
        let leaf4 = leaf_crh.hash_bytes(&leaves[3]).unwrap();

        // depth 2
        let left = two_to_one_crh.hash_bytes(&to_bytes_le![leaf1, leaf2].unwrap()).unwrap();
        let right = two_to_one_crh.hash_bytes(&to_bytes_le![leaf3, leaf4].unwrap()).unwrap();

        // depth 1
        let penultimate_left = two_to_one_crh.hash_bytes(&to_bytes_le![left, right].unwrap()).unwrap();
        let penultimate_right = parameters.hash_empty().unwrap();

        // depth 0
        two_to_one_crh.hash_bytes(&to_bytes_le![penultimate_left, penultimate_right].unwrap()).unwrap()
    };

    println!("{} == {}", merkle_tree_root, &expected_root);
    assert_eq!(merkle_tree_root, &expected_root);
}

fn merkle_path_serialization_test<P: MerkleParameters, L: ToBytes + Send + Sync + Clone + Eq>(
    leaves: &[L],
    parameters: &P,
) {
    let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
    for (i, leaf) in leaves.iter().enumerate() {
        let proof = tree.generate_proof(i, &leaf).unwrap();

        // Serialize
        let serialized = proof.to_bytes_le().unwrap();
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&serialized[..], &bincode::serialize(&proof).unwrap()[8..]);

        // Deserialize
        let deserialized = MerklePath::<P>::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, proof);
    }
}

fn merkle_path_bincode_test<P: MerkleParameters, L: ToBytes + Send + Sync + Clone + Eq>(leaves: &[L], parameters: &P) {
    let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
    for (i, leaf) in leaves.iter().enumerate() {
        let proof = tree.generate_proof(i, &leaf).unwrap();

        // Serialize
        let expected_bytes = proof.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&proof).unwrap();
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(proof, MerklePath::<P>::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(proof, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}

fn run_merkle_path_serialization_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");

    let leaves = generate_random_leaves!(4, 8);
    merkle_path_serialization_test::<P, _>(&leaves, parameters);

    let leaves = generate_random_leaves!(15, 8);
    merkle_path_serialization_test::<P, _>(&leaves, parameters);
}

fn run_merkle_path_bincode_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");

    let leaves = generate_random_leaves!(4, 8);
    merkle_path_bincode_test::<P, _>(&leaves, parameters);

    let leaves = generate_random_leaves!(15, 8);
    merkle_path_bincode_test::<P, _>(&leaves, parameters);
}

mod pedersen_crh_on_projective {
    use super::*;
    use snarkvm_curves::edwards_bls12::EdwardsProjective as Edwards;

    const NUM_WINDOWS: usize = 256;
    const WINDOW_SIZE: usize = 4;
    const LEAF_WINDOW_SIZE: usize = 2;

    type LeafCRH = PedersenCRH<Edwards, NUM_WINDOWS, LEAF_WINDOW_SIZE>;
    type TwoToOneCRH = PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>;

    #[test]
    fn empty_merkle_tree_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_empty_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn good_root_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_good_root_test::<MTParameters>();
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_bad_root_test::<MTParameters>();
    }

    #[test]
    fn depth2_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 2>;
        depth_2_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn depth3_padded_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 3>;
        padded_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn merkle_path_serialization_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_merkle_path_serialization_test::<MTParameters>();
    }

    #[test]
    fn merkle_path_bincode_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_merkle_path_bincode_test::<MTParameters>();
    }
}

mod pedersen_compressed_crh_on_projective {
    use super::*;
    use crate::merkle_tree::MerklePath;
    use snarkvm_curves::edwards_bls12::EdwardsProjective as Edwards;

    const NUM_WINDOWS: usize = 256;
    const WINDOW_SIZE: usize = 4;
    const LEAF_WINDOW_SIZE: usize = 2;

    type LeafCRH = PedersenCompressedCRH<Edwards, NUM_WINDOWS, LEAF_WINDOW_SIZE>;
    type TwoToOneCRH = PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>;

    #[test]
    fn empty_merkle_tree_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_empty_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn good_root_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_good_root_test::<MTParameters>();
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_bad_root_test::<MTParameters>();
    }

    #[test]
    fn depth2_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 2>;
        depth_2_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn depth3_padded_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 3>;
        padded_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn merkle_tree_rebuild_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        let leaves = generate_random_leaves!(1000, 32);

        let parameters = &MTParameters::setup("merkle_tree_test");
        let tree = MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &leaves[..]).unwrap();

        let mut new_tree_1 =
            MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &Vec::<[u8; 32]>::new()).unwrap();
        for (i, leaf) in leaves.iter().enumerate() {
            new_tree_1 = new_tree_1.rebuild(i, &[leaf]).unwrap();
        }

        let mut new_tree_2 =
            MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &Vec::<[u8; 32]>::new()).unwrap();
        new_tree_2 = new_tree_2.rebuild(0, &leaves[..]).unwrap();

        assert_eq!(tree.root(), new_tree_1.root());
        assert_eq!(tree.root(), new_tree_2.root());
    }

    #[test]
    fn merkle_path_serialization_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_merkle_path_serialization_test::<MTParameters>();
    }

    #[test]
    fn merkle_path_bincode_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        run_merkle_path_bincode_test::<MTParameters>();
    }

    #[should_panic]
    #[test]
    fn merkle_tree_overflow_protection_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
        let leaves = generate_random_leaves!(4, 8);

        let parameters = &MTParameters::setup("merkle_tree_test");
        let tree = MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &leaves[..]).unwrap();

        let _proof = tree.generate_proof(0, &leaves[0]).unwrap();
        _proof.verify(tree.root(), &leaves[0]).unwrap();

        let leaf1 = parameters.leaf_crh().hash_bytes(&leaves[0]).unwrap();
        let leaf2 = parameters.leaf_crh().hash_bytes(&leaves[1]).unwrap();

        // proof for non-leaf node
        let raw_nodes = to_bytes_le![leaf1, leaf2].unwrap();
        let _proof = tree.generate_proof(18446744073709551614, &raw_nodes).unwrap();
    }

    #[test]
    fn merkle_tree_invalid_path_test() {
        type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 2>;
        let leaves = generate_random_leaves!(4, 64);

        let parameters = &MTParameters::setup("merkle_tree_test");
        let leaf_crh = parameters.leaf_crh();
        let two_to_one_crh = parameters.two_to_one_crh();

        // Evaluate the Merkle tree root.
        let merkle_tree = generate_merkle_tree(&leaves, parameters);
        let merkle_tree_root = merkle_tree.root();
        // real proof
        let proof = merkle_tree.generate_proof(0, &leaves[0]).unwrap();
        assert!(proof.verify(merkle_tree_root, &leaves[0].to_vec()).unwrap());

        // Manually construct the merkle tree.

        // Construct the leaf nodes.
        let leaf1 = leaf_crh.hash_bytes(&leaves[0]).unwrap();
        let leaf2 = leaf_crh.hash_bytes(&leaves[1]).unwrap();
        let leaf3 = leaf_crh.hash_bytes(&leaves[2]).unwrap();
        let leaf4 = leaf_crh.hash_bytes(&leaves[3]).unwrap();

        // Construct the inner nodes.
        let left = two_to_one_crh.hash_bytes(&to_bytes_le![leaf1, leaf2].unwrap()).unwrap();
        let right = two_to_one_crh.hash_bytes(&to_bytes_le![leaf3, leaf4].unwrap()).unwrap();

        // Construct the root.
        let expected_root = {
            // depth 0
            two_to_one_crh.hash_bytes(&to_bytes_le![left, right].unwrap()).unwrap()
        };
        assert_eq!(merkle_tree_root, &expected_root);

        // Manually construct a proof of the inner node
        let invalid_proof = MerklePath { parameters: Arc::new(parameters.clone()), path: vec![right], leaf_index: 0 };

        // Ensure that the proof is invalid because the path length is not P::DEPTH - 1.
        assert!(!invalid_proof.verify(merkle_tree_root, &to_bytes_le![leaf1, leaf2].unwrap()).unwrap());
    }
}
