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

use super::*;
use snarkvm_console_algorithms::{Poseidon, BHP1024, BHP512};
use snarkvm_console_types::prelude::Console;

type CurrentEnvironment = Console;

const ITERATIONS: u128 = 10;

/// Runs the following test:
/// 1. Construct the Merkle tree for the leaves.
/// 2. Check that the Merkle proof for every leaf is valid.
/// 3. Add the additional leaves to the Merkle tree.
/// 4. Check that the Merkle proof for every additional leaf is valid.
fn check_merkle_tree<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>, const DEPTH: u8>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
    additional_leaves: &[LH::Leaf],
    rng: &mut TestRng,
) -> Result<()> {
    // Construct the Merkle tree for the given leaves.
    let mut merkle_tree = MerkleTree::<E, LH, PH, DEPTH>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(leaves.len(), merkle_tree.number_of_leaves);

    // Check each leaf in the Merkle tree.
    if !leaves.is_empty() {
        for (leaf_index, leaf) in leaves.iter().enumerate() {
            // Compute a Merkle proof for the leaf.
            let proof = merkle_tree.prove(leaf_index, leaf)?;
            // Verify the Merkle proof succeeds.
            assert!(proof.verify(leaf_hasher, path_hasher, merkle_tree.root(), leaf));
            // Verify the Merkle proof **fails** on an invalid root.
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::zero(), leaf));
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::one(), leaf));
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::rand(rng), leaf));
        }
    }
    // If additional leaves are provided, check that the Merkle tree is consistent with them.
    if !additional_leaves.is_empty() {
        // Append additional leaves to the Merkle tree.
        merkle_tree.append(additional_leaves)?;
        // Check each additional leaf in the Merkle tree.
        for (leaf_index, leaf) in additional_leaves.iter().enumerate() {
            // Compute a Merkle proof for the leaf.
            let proof = merkle_tree.prove(leaves.len() + leaf_index, leaf)?;
            // Verify the Merkle proof succeeds.
            assert!(proof.verify(leaf_hasher, path_hasher, merkle_tree.root(), leaf));
            // Verify the Merkle proof **fails** on an invalid root.
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::zero(), leaf));
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::one(), leaf));
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::rand(rng), leaf));
        }
    }
    Ok(())
}

/// Runs the following test:
/// 1. Construct a depth-2 Merkle tree with 4 leaves.
/// 2. Checks that every node hash and the Merkle root is correct.
fn check_merkle_tree_depth_2<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
) -> Result<()> {
    assert_eq!(4, leaves.len(), "Depth-2 test requires 4 leaves");

    // Construct the Merkle tree for the given leaves.
    let merkle_tree = MerkleTree::<E, LH, PH, 2>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(7, merkle_tree.tree.len());
    assert_eq!(4, merkle_tree.number_of_leaves);

    // Depth 2.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[3]);
    assert_eq!(expected_leaf1, merkle_tree.tree[4]);
    assert_eq!(expected_leaf2, merkle_tree.tree[5]);
    assert_eq!(expected_leaf3, merkle_tree.tree[6]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &expected_leaf0, &expected_leaf1)?;
    let expected_right = PathHash::hash_children(path_hasher, &expected_leaf2, &expected_leaf3)?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_right, merkle_tree.tree[2]);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    assert_eq!(expected_root, merkle_tree.tree[0]);
    assert_eq!(expected_root, *merkle_tree.root());
    Ok(())
}

/// Runs the following test:
/// 1. Construct a depth-3 Merkle tree with 4 leaves (leaving 4 leaves empty).
/// 2. Checks that every node hash and the Merkle root is correct.
/// 3. Add an additional leaf to the Merkle tree.
/// 4. Checks that every node hash and the Merkle root is correct.
fn check_merkle_tree_depth_3_padded<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
    additional_leaves: &[LH::Leaf],
) -> Result<()> {
    assert_eq!(4, leaves.len(), "Padded depth-3 test requires 4 leaves (out of 8)");
    assert_eq!(1, additional_leaves.len(), "Padded depth-3 test requires 1 additional leaf");

    // Construct the Merkle tree for the given leaves.
    let mut merkle_tree = MerkleTree::<E, LH, PH, 3>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(7, merkle_tree.tree.len());
    // assert_eq!(0, merkle_tree.padding_tree.len());
    assert_eq!(4, merkle_tree.number_of_leaves);

    // Depth 3.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[3]);
    assert_eq!(expected_leaf1, merkle_tree.tree[4]);
    assert_eq!(expected_leaf2, merkle_tree.tree[5]);
    assert_eq!(expected_leaf3, merkle_tree.tree[6]);

    // Depth 2.
    let expected_left = PathHash::hash_children(path_hasher, &expected_leaf0, &expected_leaf1)?;
    let expected_right = PathHash::hash_children(path_hasher, &expected_leaf2, &expected_leaf3)?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_right, merkle_tree.tree[2]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    let expected_right = path_hasher.hash_empty()?;
    assert_eq!(expected_left, merkle_tree.tree[0]);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    assert_eq!(expected_root, *merkle_tree.root());

    // ------------------------------------------------------------------------------------------ //
    // Check that the Merkle tree can be updated with the additional leaf.
    // ------------------------------------------------------------------------------------------ //

    // Rebuild the Merkle tree with the additional leaf.
    merkle_tree.append(additional_leaves)?;
    assert_eq!(15, merkle_tree.tree.len());
    // assert_eq!(0, merkle_tree.padding_tree.len());
    assert_eq!(5, merkle_tree.number_of_leaves);

    // Depth 3.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    let expected_leaf4 = LeafHash::hash_leaf(leaf_hasher, &additional_leaves[0])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[7]);
    assert_eq!(expected_leaf1, merkle_tree.tree[8]);
    assert_eq!(expected_leaf2, merkle_tree.tree[9]);
    assert_eq!(expected_leaf3, merkle_tree.tree[10]);
    assert_eq!(expected_leaf4, merkle_tree.tree[11]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[12]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[13]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[14]);

    // Depth 2.
    let expected_left0 = PathHash::hash_children(path_hasher, &expected_leaf0, &expected_leaf1)?;
    let expected_right0 = PathHash::hash_children(path_hasher, &expected_leaf2, &expected_leaf3)?;
    let expected_left1 = PathHash::hash_children(path_hasher, &expected_leaf4, &path_hasher.hash_empty()?)?;
    let expected_right1 = PathHash::hash_children(path_hasher, &path_hasher.hash_empty()?, &path_hasher.hash_empty()?)?;
    assert_eq!(expected_left0, merkle_tree.tree[3]);
    assert_eq!(expected_right0, merkle_tree.tree[4]);
    assert_eq!(expected_left1, merkle_tree.tree[5]);
    assert_eq!(expected_right1, merkle_tree.tree[6]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left0, &expected_right0)?;
    let expected_right = PathHash::hash_children(path_hasher, &expected_left1, &expected_right1)?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_right, merkle_tree.tree[2]);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    assert_eq!(expected_root, merkle_tree.tree[0]);
    assert_eq!(expected_root, *merkle_tree.root());
    Ok(())
}

/// Runs the following test:
/// 1. Construct a depth-4 Merkle tree with 4 leaves (leaving 12 leaves empty).
/// 2. Checks that every node hash and the Merkle root is correct.
/// 3. Add an additional leaf to the Merkle tree.
/// 4. Checks that every node hash and the Merkle root is correct.
/// 5. Add another additional leaf to the Merkle tree.
/// 6. Checks that every node hash and the Merkle root is correct.
fn check_merkle_tree_depth_4_padded<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
    additional_leaves: &[LH::Leaf],
) -> Result<()> {
    assert_eq!(4, leaves.len(), "Padded depth-4 test requires 4 leaves (out of 16)");
    assert_eq!(2, additional_leaves.len(), "Padded depth-4 test requires 2 additional leaves");

    // Construct the Merkle tree for the given leaves.
    let mut merkle_tree = MerkleTree::<E, LH, PH, 4>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(7, merkle_tree.tree.len());
    // assert_eq!(1, merkle_tree.padding_tree.len());
    assert_eq!(4, merkle_tree.number_of_leaves);

    // Depth 4.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[3]);
    assert_eq!(expected_leaf1, merkle_tree.tree[4]);
    assert_eq!(expected_leaf2, merkle_tree.tree[5]);
    assert_eq!(expected_leaf3, merkle_tree.tree[6]);

    // Depth 3.
    let expected_left = PathHash::hash_children(path_hasher, &expected_leaf0, &expected_leaf1)?;
    let expected_right = PathHash::hash_children(path_hasher, &expected_leaf2, &expected_leaf3)?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_right, merkle_tree.tree[2]);

    // Depth 2.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    let expected_right = path_hasher.hash_empty()?;
    assert_eq!(expected_left, merkle_tree.tree[0]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    let expected_right = path_hasher.hash_empty()?;
    // assert_eq!(expected_left, merkle_tree.padding_tree[0].0);
    // assert_eq!(path_hasher.hash_empty()?, merkle_tree.padding_tree[0].1); // Note: I don't know why the 2nd tuple element is necessary, isn't it always hash_empty?

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    assert_eq!(expected_root, *merkle_tree.root());

    // ------------------------------------------------------------------------------------------ //
    // Check that the Merkle tree can be updated with an additional leaf.
    // ------------------------------------------------------------------------------------------ //

    // Rebuild the Merkle tree with the additional leaf.
    merkle_tree.append(&[additional_leaves[0].clone()])?;
    assert_eq!(15, merkle_tree.tree.len());
    // assert_eq!(0, merkle_tree.padding_tree.len());
    assert_eq!(5, merkle_tree.number_of_leaves);

    // Depth 4.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    let expected_leaf4 = LeafHash::hash_leaf(leaf_hasher, &additional_leaves[0])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[7]);
    assert_eq!(expected_leaf1, merkle_tree.tree[8]);
    assert_eq!(expected_leaf2, merkle_tree.tree[9]);
    assert_eq!(expected_leaf3, merkle_tree.tree[10]);
    assert_eq!(expected_leaf4, merkle_tree.tree[11]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[12]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[13]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[14]);

    // Depth 3.
    let expected_left0 = PathHash::hash_children(path_hasher, &expected_leaf0, &expected_leaf1)?;
    let expected_right0 = PathHash::hash_children(path_hasher, &expected_leaf2, &expected_leaf3)?;
    let expected_left1 = PathHash::hash_children(path_hasher, &expected_leaf4, &path_hasher.hash_empty()?)?;
    let expected_right1 = PathHash::hash_children(path_hasher, &path_hasher.hash_empty()?, &path_hasher.hash_empty()?)?;
    assert_eq!(expected_left0, merkle_tree.tree[3]);
    assert_eq!(expected_right0, merkle_tree.tree[4]);
    assert_eq!(expected_left1, merkle_tree.tree[5]);
    assert_eq!(expected_right1, merkle_tree.tree[6]);

    // Depth 2.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left0, &expected_right0)?;
    let expected_right = PathHash::hash_children(path_hasher, &expected_left1, &expected_right1)?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_right, merkle_tree.tree[2]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    let expected_right = path_hasher.hash_empty()?;
    assert_eq!(expected_left, merkle_tree.tree[0]);
    assert_eq!(expected_right, path_hasher.hash_empty()?);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    assert_eq!(expected_root, *merkle_tree.root());

    // ------------------------------------------------------------------------------------------ //
    // Check that the Merkle tree can be updated with an additional leaf.
    // ------------------------------------------------------------------------------------------ //

    // Ensure we're starting where we left off from the previous rebuild.
    assert_eq!(15, merkle_tree.tree.len());
    // assert_eq!(0, merkle_tree.padding_tree.len());
    assert_eq!(5, merkle_tree.number_of_leaves);

    // Rebuild the Merkle tree with the additional leaf.
    merkle_tree.append(&[additional_leaves[1].clone()])?;
    assert_eq!(15, merkle_tree.tree.len());
    // assert_eq!(0, merkle_tree.padding_tree.len());
    assert_eq!(6, merkle_tree.number_of_leaves);

    // Depth 4.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    let expected_leaf4 = LeafHash::hash_leaf(leaf_hasher, &additional_leaves[0])?;
    let expected_leaf5 = LeafHash::hash_leaf(leaf_hasher, &additional_leaves[1])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[7]);
    assert_eq!(expected_leaf1, merkle_tree.tree[8]);
    assert_eq!(expected_leaf2, merkle_tree.tree[9]);
    assert_eq!(expected_leaf3, merkle_tree.tree[10]);
    assert_eq!(expected_leaf4, merkle_tree.tree[11]);
    assert_eq!(expected_leaf5, merkle_tree.tree[12]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[13]);
    assert_eq!(path_hasher.hash_empty()?, merkle_tree.tree[14]);

    // Depth 3.
    let expected_left0 = PathHash::hash_children(path_hasher, &expected_leaf0, &expected_leaf1)?;
    let expected_right0 = PathHash::hash_children(path_hasher, &expected_leaf2, &expected_leaf3)?;
    let expected_left1 = PathHash::hash_children(path_hasher, &expected_leaf4, &expected_leaf5)?;
    let expected_right1 = PathHash::hash_children(path_hasher, &path_hasher.hash_empty()?, &path_hasher.hash_empty()?)?;
    assert_eq!(expected_left0, merkle_tree.tree[3]);
    assert_eq!(expected_right0, merkle_tree.tree[4]);
    assert_eq!(expected_left1, merkle_tree.tree[5]);
    assert_eq!(expected_right1, merkle_tree.tree[6]);

    // Depth 2.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left0, &expected_right0)?;
    let expected_right = PathHash::hash_children(path_hasher, &expected_left1, &expected_right1)?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_right, merkle_tree.tree[2]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    let expected_right = path_hasher.hash_empty()?;
    assert_eq!(expected_left, merkle_tree.tree[0]);
    assert_eq!(expected_right, path_hasher.hash_empty()?);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &expected_left, &expected_right)?;
    assert_eq!(expected_root, *merkle_tree.root());
    Ok(())
}

#[test]
fn test_merkle_tree_bhp() -> Result<()> {
    fn run_test<const DEPTH: u8>(rng: &mut TestRng) -> Result<()> {
        type LH = BHP1024<CurrentEnvironment>;
        type PH = BHP512<CurrentEnvironment>;

        let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
        let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

        for i in 0..ITERATIONS {
            for j in 0..ITERATIONS {
                // Determine the leaves and additional leaves.
                let num_leaves = core::cmp::min(2u128.pow(DEPTH as u32), i);
                let num_additional_leaves = core::cmp::min(2u128.pow(DEPTH as u32) - num_leaves, j);

                // Check the Merkle tree.
                check_merkle_tree::<CurrentEnvironment, LH, PH, DEPTH>(
                    &leaf_hasher,
                    &path_hasher,
                    &(0..num_leaves)
                        .map(|_| Field::<CurrentEnvironment>::rand(rng).to_bits_le())
                        .collect::<Vec<Vec<bool>>>(),
                    &(0..num_additional_leaves)
                        .map(|_| Field::<CurrentEnvironment>::rand(rng).to_bits_le())
                        .collect::<Vec<Vec<bool>>>(),
                    rng,
                )?;
            }
        }
        Ok(())
    }

    let mut rng = TestRng::default();

    // Ensure DEPTH = 0 fails.
    assert!(run_test::<0>(&mut rng).is_err());
    // Spot check important depths.
    assert!(run_test::<1>(&mut rng).is_ok());
    assert!(run_test::<2>(&mut rng).is_ok());
    assert!(run_test::<3>(&mut rng).is_ok());
    assert!(run_test::<4>(&mut rng).is_ok());
    assert!(run_test::<5>(&mut rng).is_ok());
    assert!(run_test::<6>(&mut rng).is_ok());
    assert!(run_test::<7>(&mut rng).is_ok());
    assert!(run_test::<8>(&mut rng).is_ok());
    assert!(run_test::<9>(&mut rng).is_ok());
    assert!(run_test::<10>(&mut rng).is_ok());
    assert!(run_test::<15>(&mut rng).is_ok());
    assert!(run_test::<16>(&mut rng).is_ok());
    assert!(run_test::<17>(&mut rng).is_ok());
    assert!(run_test::<31>(&mut rng).is_ok());
    assert!(run_test::<32>(&mut rng).is_ok());
    assert!(run_test::<64>(&mut rng).is_ok());
    Ok(())
}

#[test]
fn test_merkle_tree_poseidon() -> Result<()> {
    fn run_test<const DEPTH: u8>(rng: &mut TestRng) -> Result<()> {
        type LH = Poseidon<CurrentEnvironment, 4>;
        type PH = Poseidon<CurrentEnvironment, 2>;

        let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
        let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

        for i in 0..ITERATIONS {
            for j in 0..ITERATIONS {
                // Determine the leaves and additional leaves.
                let num_leaves = core::cmp::min(2u128.pow(DEPTH as u32), i);
                let num_additional_leaves = core::cmp::min(2u128.pow(DEPTH as u32) - num_leaves, j);

                // Check the Merkle tree.
                check_merkle_tree::<CurrentEnvironment, LH, PH, DEPTH>(
                    &leaf_hasher,
                    &path_hasher,
                    &(0..num_leaves).map(|_| vec![Uniform::rand(rng)]).collect::<Vec<_>>(),
                    &(0..num_additional_leaves).map(|_| vec![Uniform::rand(rng)]).collect::<Vec<_>>(),
                    rng,
                )?;
            }
        }
        Ok(())
    }

    let mut rng = TestRng::default();

    // Ensure DEPTH = 0 fails.
    assert!(run_test::<0>(&mut rng).is_err());
    // Spot check important depths.
    assert!(run_test::<1>(&mut rng).is_ok());
    assert!(run_test::<2>(&mut rng).is_ok());
    assert!(run_test::<3>(&mut rng).is_ok());
    assert!(run_test::<4>(&mut rng).is_ok());
    assert!(run_test::<5>(&mut rng).is_ok());
    assert!(run_test::<6>(&mut rng).is_ok());
    assert!(run_test::<7>(&mut rng).is_ok());
    assert!(run_test::<8>(&mut rng).is_ok());
    assert!(run_test::<9>(&mut rng).is_ok());
    assert!(run_test::<10>(&mut rng).is_ok());
    assert!(run_test::<15>(&mut rng).is_ok());
    assert!(run_test::<16>(&mut rng).is_ok());
    assert!(run_test::<17>(&mut rng).is_ok());
    assert!(run_test::<31>(&mut rng).is_ok());
    assert!(run_test::<32>(&mut rng).is_ok());
    assert!(run_test::<64>(&mut rng).is_ok());
    Ok(())
}

#[test]
fn test_merkle_tree_depth_2_bhp() -> Result<()> {
    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-2 Merkle tree.
    check_merkle_tree_depth_2::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
    )
}

#[test]
fn test_merkle_tree_depth_2_poseidon() -> Result<()> {
    type LH = Poseidon<CurrentEnvironment, 4>;
    type PH = Poseidon<CurrentEnvironment, 2>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-2 Merkle tree.
    check_merkle_tree_depth_2::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
    )
}

#[test]
fn test_merkle_tree_depth_3_bhp() -> Result<()> {
    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-3 Merkle tree.
    check_merkle_tree_depth_3_padded::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
        &(0..1).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
    )
}

#[test]
fn test_merkle_tree_depth_3_poseidon() -> Result<()> {
    type LH = Poseidon<CurrentEnvironment, 4>;
    type PH = Poseidon<CurrentEnvironment, 2>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-3 Merkle tree.
    check_merkle_tree_depth_3_padded::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
        &(0..1).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
    )
}

#[test]
fn test_merkle_tree_depth_4_bhp() -> Result<()> {
    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-4 Merkle tree.
    check_merkle_tree_depth_4_padded::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
        &(0..2).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
    )
}

#[test]
fn test_merkle_tree_depth_4_poseidon() -> Result<()> {
    type LH = Poseidon<CurrentEnvironment, 4>;
    type PH = Poseidon<CurrentEnvironment, 2>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-4 Merkle tree.
    check_merkle_tree_depth_4_padded::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
        &(0..2).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
    )
}

/// Use `cargo test profiler --features timer` to run this test.
#[ignore]
#[test]
fn test_profiler() -> Result<()> {
    const DEPTH: u8 = 32;
    const NUM_LEAVES: &[usize] = &[1000, 10000];

    /// Generates the specified number of random Merkle tree leaves.
    macro_rules! generate_leaves {
        ($num_leaves:expr, $rng:expr) => {{ (0..$num_leaves).map(|_| Field::<CurrentEnvironment>::rand($rng).to_bits_le()).collect::<Vec<_>>() }};
    }

    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    for num_leaves in NUM_LEAVES {
        // New
        let leaves = generate_leaves!(*num_leaves, &mut rng);
        let mut merkle_tree =
            MerkleTree::<CurrentEnvironment, LH, PH, DEPTH>::new(&leaf_hasher, &path_hasher, &leaves)?;

        // Append
        let new_leaf = generate_leaves!(1, &mut rng);
        merkle_tree.append(&new_leaf)?;
    }

    bail!("\n\nRemember to #[ignore] this test!\n\n")
}

// fn merkle_path_serialization_test<P: MerkleParameters, L: ToBytes + Send + Sync + Clone + Eq>(
//     leaves: &[L],
//     parameters: &P,
// ) {
//     let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
//     for (i, leaf) in leaves.iter().enumerate() {
//         let proof = tree.prove(leaf_hasher, i, &leaf).unwrap();
//
//         // Serialize
//         let serialized = proof.to_bytes_le().unwrap();
//         // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
//         assert_eq!(&serialized[..], &bincode::serialize(&proof).unwrap()[8..]);
//
//         // Deserialize
//         let deserialized = MerklePath::<P>::read_le(&serialized[..]).unwrap();
//         assert_eq!(deserialized, proof);
//     }
// }
//
// fn merkle_path_bincode_test<P: MerkleParameters, L: ToBytes + Send + Sync + Clone + Eq>(leaves: &[L], parameters: &P) {
//     let tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), leaves).unwrap();
//     for (i, leaf) in leaves.iter().enumerate() {
//         let proof = tree.prove(leaf_hasher, i, &leaf).unwrap();
//
//         // Serialize
//         let expected_bytes = proof.to_bytes_le().unwrap();
//         let candidate_bytes = bincode::serialize(&proof).unwrap();
//         // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
//         assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);
//
//         // Deserialize
//         assert_eq!(proof, MerklePath::<P>::read_le(&expected_bytes[..]).unwrap());
//         assert_eq!(proof, bincode::deserialize(&candidate_bytes[..]).unwrap());
//     }
// }
//
// fn run_merkle_path_serialization_test<P: MerkleParameters>() {
//     let parameters = &P::setup("merkle_tree_test");
//
//     let leaves = generate_random_leaves!(4, 8);
//     merkle_path_serialization_test::<P, _>(&leaves, parameters);
//
//     let leaves = generate_random_leaves!(15, 8);
//     merkle_path_serialization_test::<P, _>(&leaves, parameters);
// }
//
// fn run_merkle_path_bincode_test<P: MerkleParameters>() {
//     let parameters = &P::setup("merkle_tree_test");
//
//     let leaves = generate_random_leaves!(4, 8);
//     merkle_path_bincode_test::<P, _>(&leaves, parameters);
//
//     let leaves = generate_random_leaves!(15, 8);
//     merkle_path_bincode_test::<P, _>(&leaves, parameters);
// }
//
// mod pedersen_crh_on_projective {
//     #[test]
//     fn merkle_path_serialization_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
//         run_merkle_path_serialization_test::<MTParameters>();
//     }
//
//     #[test]
//     fn merkle_path_bincode_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
//         run_merkle_path_bincode_test::<MTParameters>();
//     }
// }
//
// mod pedersen_compressed_crh_on_projective {
//     #[test]
//     fn merkle_tree_rebuild_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
//         let leaves = generate_random_leaves!(1000, 32);
//
//         let parameters = &MTParameters::setup("merkle_tree_test");
//         let tree = MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &leaves[..]).unwrap();
//
//         let mut new_tree_1 =
//             MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &Vec::<[u8; 32]>::new()).unwrap();
//         for (i, leaf) in leaves.iter().enumerate() {
//             new_tree_1 = new_tree_1.rebuild(i, &[leaf]).unwrap();
//         }
//
//         let mut new_tree_2 =
//             MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &Vec::<[u8; 32]>::new()).unwrap();
//         new_tree_2 = new_tree_2.rebuild(0, &leaves[..]).unwrap();
//
//         assert_eq!(tree.root(), new_tree_1.root());
//         assert_eq!(tree.root(), new_tree_2.root());
//     }
//
//     #[test]
//     fn merkle_path_serialization_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
//         run_merkle_path_serialization_test::<MTParameters>();
//     }
//
//     #[test]
//     fn merkle_path_bincode_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
//         run_merkle_path_bincode_test::<MTParameters>();
//     }
//
//     #[should_panic]
//     #[test]
//     fn merkle_tree_overflow_protection_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 32>;
//         let leaves = generate_random_leaves!(4, 8);
//
//         let parameters = &MTParameters::setup("merkle_tree_test");
//         let tree = MerkleTree::<MTParameters>::new(Arc::new(parameters.clone()), &leaves[..]).unwrap();
//
//         let _proof = tree.prove(leaf_hasher, 0, &leaves[0]).unwrap();
//         _proof.verify(tree.root(), &leaves[0]).unwrap();
//
//         let leaf1 = parameters.leaf_crh().hash_bytes(&leaves[0]).unwrap();
//         let leaf2 = parameters.leaf_crh().hash_bytes(&leaves[1]).unwrap();
//
//         // proof for non-leaf node
//         let raw_nodes = to_bytes_le![leaf1, leaf2].unwrap();
//         let _proof = tree.prove(leaf_hasher, 18446744073709551614, &raw_nodes).unwrap();
//     }
//
//     #[test]
//     fn merkle_tree_invalid_path_test() {
//         type MTParameters = MerkleTreeParameters<LeafCRH, TwoToOneCRH, 2>;
//         let leaves = generate_random_leaves!(4, 64);
//
//         let parameters = &MTParameters::setup("merkle_tree_test");
//         let leaf_crh = parameters.leaf_crh();
//         let two_to_one_crh = parameters.two_to_one_crh();
//
//         // Evaluate the Merkle tree root.
//         let merkle_tree = generate_merkle_tree(&leaves, parameters);
//         let merkle_tree_root = merkle_tree.root();
//         // real proof
//         let proof = merkle_tree.prove(leaf_hasher, 0, &leaves[0]).unwrap();
//         assert!(proof.verify(merkle_tree_root, &leaves[0].to_vec()).unwrap());
//
//         // Manually construct the merkle tree.
//
//         // Construct the leaf nodes.
//         let leaf1 = leaf_crh.hash_bytes(&leaves[0]).unwrap();
//         let leaf2 = leaf_crh.hash_bytes(&leaves[1]).unwrap();
//         let leaf3 = leaf_crh.hash_bytes(&leaves[2]).unwrap();
//         let leaf4 = leaf_crh.hash_bytes(&leaves[3]).unwrap();
//
//         // Construct the inner nodes.
//         let left = two_to_one_crh.hash_bytes(&to_bytes_le![leaf1, leaf2].unwrap()).unwrap();
//         let right = two_to_one_crh.hash_bytes(&to_bytes_le![leaf3, leaf4].unwrap()).unwrap();
//
//         // Construct the root.
//         let expected_root = {
//             // depth 0
//             two_to_one_crh.hash_bytes(&to_bytes_le![left, right].unwrap()).unwrap()
//         };
//         assert_eq!(merkle_tree_root, &expected_root);
//
//         // Manually construct a proof of the inner node
//         let invalid_proof = MerklePath { parameters: Arc::new(parameters.clone()), path: vec![right], leaf_index: 0 };
//
//         // Ensure that the proof is invalid because the path length is not P::DEPTH - 1.
//         assert!(!invalid_proof.verify(merkle_tree_root, &to_bytes_le![leaf1, leaf2].unwrap()).unwrap());
//     }
// }
