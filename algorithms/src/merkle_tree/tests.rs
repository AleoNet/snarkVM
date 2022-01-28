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
        assert!(proof.verify(&<P::H as CRH>::Output::default(), &leaf).unwrap());
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
    let crh = parameters.crh();

    // Evaluate the Merkle tree root.
    let leaves = generate_random_leaves!(4, 64);
    let merkle_tree = generate_merkle_tree(&leaves, parameters);
    let merkle_tree_root = merkle_tree.root();

    // Evaluate the root by direct hashing.
    let expected_root = {
        // depth 2
        let leaf1 = crh.hash(&leaves[0]).unwrap();
        let leaf2 = crh.hash(&leaves[1]).unwrap();
        let leaf3 = crh.hash(&leaves[2]).unwrap();
        let leaf4 = crh.hash(&leaves[3]).unwrap();

        // depth 1
        let left = crh.hash(&to_bytes_le![leaf1, leaf2].unwrap()).unwrap();
        let right = crh.hash(&to_bytes_le![leaf3, leaf4].unwrap()).unwrap();

        // depth 0
        crh.hash(&to_bytes_le![left, right].unwrap()).unwrap()
    };

    println!("{} == {}", merkle_tree_root, &expected_root);
    assert_eq!(merkle_tree_root, &expected_root);
}

fn padded_merkle_tree_test<P: MerkleParameters>() {
    let parameters = &P::setup("merkle_tree_test");
    let crh = parameters.crh();

    // Evaluate the Merkle tree root

    let leaves = generate_random_leaves!(4, 64);
    let merkle_tree = generate_merkle_tree(&leaves, parameters);
    let merkle_tree_root = merkle_tree.root();

    // Evaluate the root by direct hashing.
    let expected_root = {
        // depth 3
        let leaf1 = crh.hash(&leaves[0]).unwrap();
        let leaf2 = crh.hash(&leaves[1]).unwrap();
        let leaf3 = crh.hash(&leaves[2]).unwrap();
        let leaf4 = crh.hash(&leaves[3]).unwrap();

        // depth 2
        let left = crh.hash(&to_bytes_le![leaf1, leaf2].unwrap()).unwrap();
        let right = crh.hash(&to_bytes_le![leaf3, leaf4].unwrap()).unwrap();

        // depth 1
        let penultimate_left = crh.hash(&to_bytes_le![left, right].unwrap()).unwrap();
        let penultimate_right = parameters.hash_empty().unwrap();

        // depth 0
        crh.hash(&to_bytes_le![penultimate_left, penultimate_right].unwrap())
            .unwrap()
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

    #[test]
    fn empty_merkle_tree_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_empty_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn good_root_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_good_root_test::<MTParameters>();
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_bad_root_test::<MTParameters>();
    }

    #[test]
    fn depth2_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 2>;
        depth_2_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn depth3_padded_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 3>;
        padded_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn merkle_path_serialization_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_merkle_path_serialization_test::<MTParameters>();
    }

    #[test]
    fn merkle_path_bincode_test() {
        type MTParameters = MerkleTreeParameters<PedersenCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_merkle_path_bincode_test::<MTParameters>();
    }
}

mod pedersen_compressed_crh_on_projective {
    use super::*;
    use snarkvm_curves::edwards_bls12::EdwardsProjective as Edwards;

    const NUM_WINDOWS: usize = 256;
    const WINDOW_SIZE: usize = 4;

    #[test]
    fn empty_merkle_tree_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_empty_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn good_root_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_good_root_test::<MTParameters>();
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_bad_root_test::<MTParameters>();
    }

    #[test]
    fn depth2_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 2>;
        depth_2_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn depth3_padded_merkle_tree_matches_hashing_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 3>;
        padded_merkle_tree_test::<MTParameters>();
    }

    #[test]
    fn merkle_tree_rebuild_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
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
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_merkle_path_serialization_test::<MTParameters>();
    }

    #[test]
    fn merkle_path_bincode_test() {
        type MTParameters = MerkleTreeParameters<PedersenCompressedCRH<Edwards, NUM_WINDOWS, WINDOW_SIZE>, 32>;
        run_merkle_path_bincode_test::<MTParameters>();
    }
}
