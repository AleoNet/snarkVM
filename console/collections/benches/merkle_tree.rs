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

#[macro_use]
extern crate criterion;

use snarkvm_console_network::{
    prelude::{TestRng, ToBits, Uniform},
    Network,
    Testnet3,
};
use snarkvm_console_types::Field;

use criterion::{BenchmarkId, Criterion};

const DEPTH: u8 = 32;

// const NUM_LEAVES: &[usize] = &[1, 10, 100, 1_000, 10_000, 100_000, 1_000_000];
const NUM_LEAVES: &[usize] = &[1_000_000];
const APPEND_SIZES: &[usize] = &[1, 10, 100, 1_000, 10_000, 100_000, 1_000_000];
const UPDATE_SIZES: &[usize] = &[1, 10, 100, 1_000, 10_000, 100_000, 1_000_000];

/// Generates the specified number of random Merkle tree leaves.
macro_rules! generate_leaves {
    ($num_leaves:expr, $rng:expr) => {{ (0..$num_leaves).map(|_| Field::<Testnet3>::rand($rng).to_bits_le()).collect::<Vec<_>>() }};
}

fn new(c: &mut Criterion) {
    let mut rng = TestRng::default();
    // Accumulate leaves in a vector to avoid recomputing across iterations.
    let mut leaves = vec![];
    for num_leaves in NUM_LEAVES {
        // Generate the required number of leaves.
        leaves.extend(generate_leaves!(num_leaves - leaves.len(), &mut rng));
        // Benchmark the creation of a Merkle tree with the specified number of leaves.
        c.bench_function(&format!("MerkleTree/new/{num_leaves}"), |b| {
            b.iter_batched_ref(
                || leaves.clone(),
                | leaves | { let _tree = Testnet3::merkle_tree_bhp::<DEPTH>(leaves).unwrap(); },
                criterion::BatchSize::LargeInput,
            )
        });
    }
}

fn append(c: &mut Criterion) {
    let mut rng = TestRng::default();
    // Accumulate leaves in a vector to avoid recomputing across iterations.
    let mut leaves = vec![];
    for num_leaves in NUM_LEAVES {
        leaves.extend(generate_leaves!(leaves.len() - num_leaves, &mut rng));
        // Construct a Merkle tree with the specified number of leaves.
        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        // Generate all of the leaves that will be appended to the tree.
        let new_leaves = generate_leaves!(*APPEND_SIZES.last().unwrap(), &mut rng);
        // For each number of leaves to append, benchmark the append operation.
        for num_new_leaves in APPEND_SIZES {
            c.bench_function(&format!("MerkleTree/append/{num_leaves}/{num_new_leaves}"), |b| {
                b.iter_with_setup(
                    || merkle_tree.clone(),
                    |mut merkle_tree| {
                        merkle_tree.append(&new_leaves[..*num_leaves]).unwrap();
                    },
                )
            });
        }
    }
}

fn update(c: &mut Criterion) {
    let mut rng = TestRng::default();
    // Accumulate leaves in a vector to avoid recomputing across iterations.
    let mut leaves = vec![];
    for num_leaves in NUM_LEAVES {
        leaves.extend(generate_leaves!(leaves.len() - num_leaves, &mut rng));
        // Construct a Merkle tree with the specified number of leaves.
        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        // Generate all of the updates that will be applied to the tree.
        let new_leaves = generate_leaves!(*UPDATE_SIZES.last().unwrap(), &mut rng);
        let updates = new_leaves
            .iter()
            .map(|leaf| {
                let index: usize = Uniform::rand(&mut rng);
                (index % num_leaves, leaf)
            })
            .collect::<Vec<_>>();
        // For each number of leaves to update, benchmark the update operation.
        for num_new_leaves in UPDATE_SIZES {
            c.bench_function(&format!("MerkleTree/update/{num_leaves}/{num_new_leaves}"), |b| {
                b.iter_with_setup(
                    || merkle_tree.clone(),
                    |mut merkle_tree| {
                        for (index, new_leaf) in updates.iter().take(*num_new_leaves) {
                            merkle_tree.update(*index, new_leaf).unwrap();
                        }
                    },
                )
            });
        }
    }
}

fn batch_update(c: &mut Criterion) {
    let mut rng = TestRng::default();
    // Accumulate leaves in a vector to avoid recomputing across iterations.
    let mut leaves = vec![];
    for num_leaves in NUM_LEAVES {
        leaves.extend(generate_leaves!(leaves.len() - num_leaves, &mut rng));
        // Construct a Merkle tree with the specified number of leaves.
        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        // Generate all of the updates that will be applied to the tree.
        // Note that we generate 2 * MAX_UPDATE_SIZE leaves to increase the number of unique of updates.
        let new_leaves = generate_leaves!(2 * *UPDATE_SIZES.last().unwrap(), &mut rng);
        let mut updates = new_leaves
            .into_iter()
            .map(|leaf| {
                let index: usize = Uniform::rand(&mut rng);
                (index % num_leaves, leaf)
            })
            .collect::<Vec<_>>();
        updates.sort_by(|(a, _), (b, _)| a.cmp(b));
        updates.reverse();
        updates.dedup_by_key(|(a, _)| *a);

        // For each number of leaves to update, benchmark the update operation.
        for num_new_leaves in UPDATE_SIZES {
            let num_new_leaves = std::cmp::min(*num_new_leaves, updates.len());
            c.bench_function(&format!("MerkleTree/batch_update/{num_leaves}/{num_new_leaves}",), |b| {
                b.iter_with_setup(
                    || merkle_tree.clone(),
                    |mut merkle_tree| {
                        merkle_tree.batch_update(&updates[..num_new_leaves]).unwrap();
                    },
                )
            });
        }
    }
}

fn compare_single_leaf_update(c: &mut Criterion) {
    let mut group = c.benchmark_group("SingleLeafUpdate");
    let mut rng = TestRng::default();
    // Accumulate leaves in a vector to avoid recomputing across iterations.
    let mut leaves = vec![];
    for depth in 1..=15 {
        let num_leaves = 2usize.saturating_pow(depth as u32);
        leaves.extend(generate_leaves!(num_leaves - leaves.len(), &mut rng));
        // Construct a Merkle tree with the specified number of leaves.
        let tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        // Generate a new leaf and select a random index to update.
        let index: usize = Uniform::rand(&mut rng);
        let index = index % num_leaves;
        let new_leaf = generate_leaves!(1, &mut rng).pop().unwrap();

        group.bench_with_input(
            BenchmarkId::new("Standard", &format!("{depth}")),
            &new_leaf,
            |b, new_leaf| b.iter_with_setup(|| tree.clone(), |mut tree| tree.update(index, new_leaf))
        );
        group.bench_with_input(
            BenchmarkId::new("Batch", &format!("{depth}")),
            &vec![(index, new_leaf)],
            |b, updates| b.iter_with_setup(|| tree.clone(), |mut tree| tree.batch_update(&updates)),
        );
    }
}

criterion_group! {
    name = merkle_tree;
    config = Criterion::default().sample_size(10);
    targets = new, append, update, batch_update, compare_single_leaf_update,
}
criterion_main!(merkle_tree);
