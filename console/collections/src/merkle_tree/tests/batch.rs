// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use super::*;
use snarkvm_console_algorithms::{Poseidon, BHP1024, BHP512};
use snarkvm_console_types::prelude::Console;

type CurrentEnvironment = Console;

const ITERATIONS: u128 = 10;

/// Runs the following test:
/// 1. Construct the Merkle tree for the leaves.
/// 2. Check that the Merkle proof for every leaf is valid.
/// 3. Update leaves in the Merkle tree.
/// 4. Check that the Merkle proof for every leaf is valid.
fn check_merkle_tree<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>, const DEPTH: u8>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
    updates: &[(usize, LH::Leaf)],
) -> Result<()> {
    // Construct the Merkle tree for the given leaves.
    let mut merkle_tree = MerkleTree::<E, LH, PH, DEPTH>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(leaves.len(), merkle_tree.number_of_leaves);

    let mut rng = TestRng::default();

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
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::rand(&mut rng), leaf));
        }
    }

    // If additional leaves are provided, check that the Merkle tree is consistent with them.
    if !updates.is_empty() {
        println!("Updating leaves.");
        // Update the leaves of the Merkle tree.
        merkle_tree.batch_update(updates)?;
        println!("Checking updated leaves.");
        // Check each additional leaf in the Merkle tree.
        for (leaf_index, leaf) in updates {
            println!("1");
            // Compute a Merkle proof for the leaf.
            let proof = merkle_tree.prove(*leaf_index, leaf)?;
            println!("2");
            // Verify the Merkle proof succeeds.
            assert!(proof.verify(leaf_hasher, path_hasher, merkle_tree.root(), leaf));
            println!("3");
            // Verify the Merkle proof **fails** on an invalid root.
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::zero(), leaf));
            println!("4");
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::one(), leaf));
            println!("5");
            assert!(!proof.verify(leaf_hasher, path_hasher, &PH::Hash::rand(&mut rng), leaf));
            println!("6");
        }
    }
    Ok(())
}

/// Runs the following test:
/// 1. Construct a depth-3 Merkle tree with 4 leaves (leaving 4 leaves empty).
/// 2. Checks that every node hash and the Merkle root is correct.
/// 3. Updates a leaf in the Merkle tree.
/// 4. Checks that every node hash and the Merkle root is correct.
fn check_merkle_tree_depth_3_single_update<
    E: Environment,
    LH: LeafHash<Hash = PH::Hash>,
    PH: PathHash<Hash = Field<E>>,
>(
    leaf_hasher: &LH,
    path_hasher: &PH,
    leaves: &[LH::Leaf],
    updates: &[(usize, LH::Leaf)],
) -> Result<()> {
    assert_eq!(4, leaves.len(), "Padded depth-3 test requires 4 leaves (out of 8)");
    assert_eq!(1, updates.len(), "Padded depth-3 test requires 1 update");

    // Construct the Merkle tree for the given leaves.
    let mut merkle_tree = MerkleTree::<E, LH, PH, 3>::new(leaf_hasher, path_hasher, leaves)?;
    assert_eq!(7, merkle_tree.tree.len());
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
    // Check that the Merkle tree can be updated in place with the new leaf.
    // ------------------------------------------------------------------------------------------ //

    // Update the Merkle tree.
    let (leaf_index, leaf) = &updates[0];
    merkle_tree.batch_update(updates)?;
    assert_eq!(7, merkle_tree.tree.len());
    assert_eq!(4, merkle_tree.number_of_leaves);

    // Depth 3.
    let expected_leaf0 = match *leaf_index == 0 {
        true => LeafHash::hash_leaf(leaf_hasher, leaf)?,
        false => LeafHash::hash_leaf(leaf_hasher, &leaves[0])?,
    };
    let expected_leaf1 = match *leaf_index == 1 {
        true => LeafHash::hash_leaf(leaf_hasher, leaf)?,
        false => LeafHash::hash_leaf(leaf_hasher, &leaves[1])?,
    };
    let expected_leaf2 = match *leaf_index == 2 {
        true => LeafHash::hash_leaf(leaf_hasher, leaf)?,
        false => LeafHash::hash_leaf(leaf_hasher, &leaves[2])?,
    };
    let expected_leaf3 = match *leaf_index == 3 {
        true => LeafHash::hash_leaf(leaf_hasher, leaf)?,
        false => LeafHash::hash_leaf(leaf_hasher, &leaves[3])?,
    };
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
                let num_updates = core::cmp::min(num_leaves, core::cmp::min(2u128.pow(DEPTH as u32) - num_leaves, j));

                println!("num_leaves: {}, num_updates: {}", num_leaves, num_updates);

                // Check the Merkle tree.
                check_merkle_tree::<CurrentEnvironment, LH, PH, DEPTH>(
                    &leaf_hasher,
                    &path_hasher,
                    &(0..num_leaves)
                        .map(|_| Field::<CurrentEnvironment>::rand(rng).to_bits_le())
                        .collect::<Vec<Vec<bool>>>(),
                    &(0..num_updates)
                        .rev()
                        .map(|i| ((i % num_leaves) as usize, Field::<CurrentEnvironment>::rand(rng).to_bits_le()))
                        .collect::<Vec<(usize, Vec<bool>)>>(),
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
                let num_additional_leaves =
                    core::cmp::min(num_leaves, core::cmp::min(2u128.pow(DEPTH as u32) - num_leaves, j));

                // Check the Merkle tree.
                check_merkle_tree::<CurrentEnvironment, LH, PH, DEPTH>(
                    &leaf_hasher,
                    &path_hasher,
                    &(0..num_leaves).map(|_| vec![Uniform::rand(rng)]).collect::<Vec<_>>(),
                    &(0..num_additional_leaves)
                        .rev()
                        .map(|i| ((i % num_leaves) as usize, vec![Uniform::rand(rng)]))
                        .collect::<Vec<_>>(),
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
fn test_merkle_tree_depth_3_bhp() -> Result<()> {
    type LH = BHP1024<CurrentEnvironment>;
    type PH = BHP512<CurrentEnvironment>;

    let leaf_hasher = LH::setup("AleoMerkleTreeTest0")?;
    let path_hasher = PH::setup("AleoMerkleTreeTest1")?;

    let mut rng = TestRng::default();

    // Check the depth-3 Merkle tree.
    check_merkle_tree_depth_3_single_update::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()).collect::<Vec<Vec<bool>>>(),
        &(0..1)
            .rev()
            .map(|i| (i, Field::<CurrentEnvironment>::rand(&mut rng).to_bits_le()))
            .collect::<Vec<(usize, Vec<bool>)>>(),
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
    check_merkle_tree_depth_3_single_update::<CurrentEnvironment, LH, PH>(
        &leaf_hasher,
        &path_hasher,
        &(0..4).map(|_| vec![Uniform::rand(&mut rng)]).collect::<Vec<_>>(),
        &(0..1).rev().map(|i| (i, vec![Uniform::rand(&mut rng)])).collect::<Vec<_>>(),
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

        // Update
        generate_leaves!(1, &mut rng)
            .into_iter()
            .map(|leaf| {
                let index: usize = Uniform::rand(&mut rng);
                (index % num_leaves, leaf)
            })
            .for_each(|(index, leaf)| {
                merkle_tree.batch_update(&[(index, leaf)]).unwrap();
            });
    }

    bail!("\n\nRemember to #[ignore] this test!\n\n")
}
