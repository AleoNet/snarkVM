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

/// Runs the following test:
/// 1. Construct a depth-2 arity-3 Merkle tree with 9 leaves.
/// 2. Checks that every node hash and the Merkle root is correct.
fn check_merkle_tree_depth_2_arity_3<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
) -> Result<()> {
    assert_eq!(9, leaves.len(), "Depth-2 test requires 9 leaves");

    // Construct the Merkle tree for the given leaves.
    let merkle_tree = MultiArityMerkleTree::<E, LH, PH, 2, 3>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(13, merkle_tree.tree.len());
    assert_eq!(9, merkle_tree.number_of_leaves);

    // Depth 2.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    let expected_leaf4 = LeafHash::hash_leaf(leaf_hasher, &leaves[4])?;
    let expected_leaf5 = LeafHash::hash_leaf(leaf_hasher, &leaves[5])?;
    let expected_leaf6 = LeafHash::hash_leaf(leaf_hasher, &leaves[6])?;
    let expected_leaf7 = LeafHash::hash_leaf(leaf_hasher, &leaves[7])?;
    let expected_leaf8 = LeafHash::hash_leaf(leaf_hasher, &leaves[8])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[4]);
    assert_eq!(expected_leaf1, merkle_tree.tree[5]);
    assert_eq!(expected_leaf2, merkle_tree.tree[6]);
    assert_eq!(expected_leaf3, merkle_tree.tree[7]);
    assert_eq!(expected_leaf4, merkle_tree.tree[8]);
    assert_eq!(expected_leaf5, merkle_tree.tree[9]);
    assert_eq!(expected_leaf6, merkle_tree.tree[10]);
    assert_eq!(expected_leaf7, merkle_tree.tree[11]);
    assert_eq!(expected_leaf8, merkle_tree.tree[12]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &[expected_leaf0, expected_leaf1, expected_leaf2])?;
    let expected_middle = PathHash::hash_children(path_hasher, &[expected_leaf3, expected_leaf4, expected_leaf5])?;
    let expected_right = PathHash::hash_children(path_hasher, &[expected_leaf6, expected_leaf7, expected_leaf8])?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_middle, merkle_tree.tree[2]);
    assert_eq!(expected_right, merkle_tree.tree[3]);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &[expected_left, expected_middle, expected_right])?;
    assert_eq!(expected_root, merkle_tree.tree[0]);
    assert_eq!(expected_root, *merkle_tree.root());
    Ok(())
}

/// Runs the following test:
/// 1. Construct a depth-3 Merkle tree with 10 leaves (leaving 17 leaves empty).
/// 2. Checks that every node hash and the Merkle root is correct.
fn check_merkle_tree_depth_3_arity_3_padded<
    E: Environment,
    LH: LeafHash<Hash = PH::Hash>,
    PH: PathHash<Hash = Field<E>>,
>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
) -> Result<()> {
    assert_eq!(10, leaves.len(), "Padded depth-3 test requires 10 leaves (out of 27)");

    const ARITY: u8 = 3;

    // Construct the Merkle tree for the given leaves.
    let merkle_tree = MultiArityMerkleTree::<E, LH, PH, 3, ARITY>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(40, merkle_tree.tree.len());
    assert_eq!(10, merkle_tree.number_of_leaves);

    // Depth 3.
    let expected_leaf0 = LeafHash::hash_leaf(leaf_hasher, &leaves[0])?;
    let expected_leaf1 = LeafHash::hash_leaf(leaf_hasher, &leaves[1])?;
    let expected_leaf2 = LeafHash::hash_leaf(leaf_hasher, &leaves[2])?;
    let expected_leaf3 = LeafHash::hash_leaf(leaf_hasher, &leaves[3])?;
    let expected_leaf4 = LeafHash::hash_leaf(leaf_hasher, &leaves[4])?;
    let expected_leaf5 = LeafHash::hash_leaf(leaf_hasher, &leaves[5])?;
    let expected_leaf6 = LeafHash::hash_leaf(leaf_hasher, &leaves[6])?;
    let expected_leaf7 = LeafHash::hash_leaf(leaf_hasher, &leaves[7])?;
    let expected_leaf8 = LeafHash::hash_leaf(leaf_hasher, &leaves[8])?;
    let expected_leaf9 = LeafHash::hash_leaf(leaf_hasher, &leaves[9])?;
    assert_eq!(expected_leaf0, merkle_tree.tree[13]);
    assert_eq!(expected_leaf1, merkle_tree.tree[14]);
    assert_eq!(expected_leaf2, merkle_tree.tree[15]);
    assert_eq!(expected_leaf3, merkle_tree.tree[16]);
    assert_eq!(expected_leaf4, merkle_tree.tree[17]);
    assert_eq!(expected_leaf5, merkle_tree.tree[18]);
    assert_eq!(expected_leaf6, merkle_tree.tree[19]);
    assert_eq!(expected_leaf7, merkle_tree.tree[20]);
    assert_eq!(expected_leaf8, merkle_tree.tree[21]);
    assert_eq!(expected_leaf9, merkle_tree.tree[22]);
    for i in 23..40 {
        assert_eq!(path_hasher.hash_empty::<ARITY>()?, merkle_tree.tree[i]);
    }

    // Depth 2.
    let expected_left0 = PathHash::hash_children(path_hasher, &[expected_leaf0, expected_leaf1, expected_leaf2])?;
    let expected_middle0 = PathHash::hash_children(path_hasher, &[expected_leaf3, expected_leaf4, expected_leaf5])?;
    let expected_right0 = PathHash::hash_children(path_hasher, &[expected_leaf6, expected_leaf7, expected_leaf8])?;
    assert_eq!(expected_left0, merkle_tree.tree[4]);
    assert_eq!(expected_middle0, merkle_tree.tree[5]);
    assert_eq!(expected_right0, merkle_tree.tree[6]);

    let expected_left1 = PathHash::hash_children(path_hasher, &[
        expected_leaf9,
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
    ])?;
    let expected_middle1 = PathHash::hash_children(path_hasher, &[
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
    ])?;
    let expected_right1 = PathHash::hash_children(path_hasher, &[
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
    ])?;
    assert_eq!(expected_left1, merkle_tree.tree[7]);
    assert_eq!(expected_middle1, merkle_tree.tree[8]);
    assert_eq!(expected_right1, merkle_tree.tree[9]);

    let expected_left2 = PathHash::hash_children(path_hasher, &[
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
    ])?;
    let expected_middle2 = PathHash::hash_children(path_hasher, &[
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
    ])?;
    let expected_right2 = PathHash::hash_children(path_hasher, &[
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
        path_hasher.hash_empty::<ARITY>()?,
    ])?;
    assert_eq!(expected_left2, merkle_tree.tree[10]);
    assert_eq!(expected_middle2, merkle_tree.tree[11]);
    assert_eq!(expected_right2, merkle_tree.tree[12]);

    // Depth 1.
    let expected_left = PathHash::hash_children(path_hasher, &[expected_left0, expected_middle0, expected_right0])?;
    let expected_middle = PathHash::hash_children(path_hasher, &[expected_left1, expected_middle1, expected_right1])?;
    let expected_right = PathHash::hash_children(path_hasher, &[expected_left2, expected_middle2, expected_right2])?;
    assert_eq!(expected_left, merkle_tree.tree[1]);
    assert_eq!(expected_middle, merkle_tree.tree[2]);
    assert_eq!(expected_right, merkle_tree.tree[3]);

    // Depth 0.
    let expected_root = PathHash::hash_children(path_hasher, &[expected_left, expected_middle, expected_right])?;
    assert_eq!(expected_root, *merkle_tree.root());

    Ok(())
}

#[test]
fn test_merkle_tree_depth_2_arity_3_bhp() -> Result<()> {
    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-2 arity-3 Merkle tree.
    check_merkle_tree_depth_2_arity_3::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..9).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
    )
}

#[test]
fn test_merkle_tree_depth_2_arity_3_poseidon() -> Result<()> {
    type LH = Poseidon<CurrentEnvironment, 4>;
    type PH = Poseidon<CurrentEnvironment, 3>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-2 arity-3 Merkle tree.
    check_merkle_tree_depth_2_arity_3::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..9).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
    )
}

#[test]
fn test_merkle_tree_depth_3_arity_3_padded_bhp() -> Result<()> {
    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-2 arity-3 Merkle tree.
    check_merkle_tree_depth_3_arity_3_padded::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..10).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
    )
}

#[test]
fn test_merkle_tree_depth_3_arity_3_poseidon() -> Result<()> {
    type LH = Poseidon<CurrentEnvironment, 4>;
    type PH = Poseidon<CurrentEnvironment, 3>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-3 arity-3 Merkle tree.
    check_merkle_tree_depth_3_arity_3_padded::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..10).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
    )
}
