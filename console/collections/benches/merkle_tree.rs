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

const NUM_LEAVES: &[usize] = &[1, 10, 100, 1000, 10000];
const APPEND_SIZES: &[usize] = &[10, 100, 1000];
const UPDATE_SIZES: &[usize] = &[10, 100, 1000];

/// Generates the specified number of random Merkle tree leaves.
macro_rules! generate_leaves {
    ($num_leaves:expr, $rng:expr) => {{ (0..$num_leaves).map(|_| Field::<Testnet3>::rand($rng).to_bits_le()).collect::<Vec<_>>() }};
}

fn new(c: &mut Criterion) {
    let mut rng = TestRng::default();

    for num_leaves in NUM_LEAVES {
        let leaves = generate_leaves!(*num_leaves, &mut rng);

        c.bench_function(&format!("MerkleTree::new ({num_leaves} leaves)"), move |b| {
            b.iter(|| {
                let _tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
            })
        });
    }
}

fn append(c: &mut Criterion) {
    let mut rng = TestRng::default();

    for num_leaves in NUM_LEAVES {
        let leaves = generate_leaves!(*num_leaves, &mut rng);

        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        let new_leaf = generate_leaves!(1, &mut rng);

        c.bench_function(
            &format!("MerkleTree::append (adding single leaf to a tree with {num_leaves} leaves)"),
            move |b| {
                b.iter_with_setup(
                    || merkle_tree.clone(),
                    |mut merkle_tree| {
                        merkle_tree.append(&new_leaf).unwrap();
                    },
                )
            },
        );

        for num_new_leaves in APPEND_SIZES {
            let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
            let new_leaves = generate_leaves!(*num_new_leaves, &mut rng);

            c.bench_function(
                &format!("MerkleTree::append (adding {num_new_leaves} new leaves to a tree with {num_leaves} leaves)"),
                move |b| {
                    b.iter_with_setup(
                        || merkle_tree.clone(),
                        |mut merkle_tree| {
                            merkle_tree.append(&new_leaves).unwrap();
                        },
                    )
                },
            );
        }
    }
}

fn update(c: &mut Criterion) {
    let mut rng = TestRng::default();

    for num_leaves in NUM_LEAVES {
        let leaves = generate_leaves!(*num_leaves, &mut rng);

        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        let index: usize = Uniform::rand(&mut rng);
        let new_leaf = generate_leaves!(1, &mut rng);

        c.bench_function(
            &format!("MerkleTree::update (updating a single leaf in a tree with {num_leaves} leaves)"),
            move |b| {
                b.iter_with_setup(
                    || merkle_tree.clone(),
                    |mut merkle_tree| {
                        merkle_tree.update(index % num_leaves, &new_leaf[0]).unwrap();
                    },
                )
            },
        );

        for num_new_leaves in UPDATE_SIZES {
            let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
            let new_leaves = generate_leaves!(*num_new_leaves, &mut rng);
            let updates = new_leaves
                .iter()
                .map(|leaf| {
                    let index: usize = Uniform::rand(&mut rng);
                    (index % num_leaves, leaf)
                })
                .collect::<Vec<_>>();

            c.bench_function(
                &format!("MerkleTree::update (updating {num_new_leaves} leaves in a tree with {num_leaves} leaves)"),
                move |b| {
                    b.iter_with_setup(
                        || merkle_tree.clone(),
                        |mut merkle_tree| {
                            for (index, new_leaf) in updates.iter() {
                                merkle_tree.update(*index, new_leaf).unwrap();
                            }
                        },
                    )
                },
            );
        }
    }
}

fn batch_update(c: &mut Criterion) {
    let mut rng = TestRng::default();

    for num_leaves in NUM_LEAVES {
        let leaves = generate_leaves!(*num_leaves, &mut rng);

        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        let mut new_leaf = generate_leaves!(1, &mut rng);
        let index: usize = Uniform::rand(&mut rng);
        let updates = vec![(index % num_leaves, new_leaf.pop().unwrap())];

        c.bench_function(
            &format!("MerkleTree::batch_update (updating a single leaf in a tree with {num_leaves} leaves)"),
            move |b| {
                b.iter_with_setup(
                    || merkle_tree.clone(),
                    |mut merkle_tree| {
                        merkle_tree.batch_update(&updates).unwrap();
                    },
                )
            },
        );

        for num_new_leaves in UPDATE_SIZES {
            let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
            let new_leaves = generate_leaves!(*num_new_leaves, &mut rng);

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

            c.bench_function(
                &format!(
                    "MerkleTree::batch_update (updating {} leaves in a tree with {num_leaves} leaves)",
                    updates.len()
                ),
                move |b| {
                    b.iter_with_setup(
                        || merkle_tree.clone(),
                        |mut merkle_tree| {
                            merkle_tree.batch_update(&updates).unwrap();
                        },
                    )
                },
            );
        }
    }
}

fn compare_single_leaf_update(c: &mut Criterion) {
    let mut group = c.benchmark_group("Single");
    let mut rng = TestRng::default();
    for depth in 1..=15 {
        let num_leaves = 2usize.saturating_pow(depth as u32);
        let leaves = generate_leaves!(num_leaves, &mut rng);

        let index: usize = Uniform::rand(&mut rng);
        let index = index % num_leaves;

        let new_leaf = generate_leaves!(1, &mut rng).pop().unwrap();

        let mut tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        group.bench_with_input(BenchmarkId::new("Standard", &format!("DEPTH: {depth}")), &new_leaf, |b, new_leaf| {
            b.iter(|| tree.update(index, new_leaf))
        });

        let mut tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        group.bench_with_input(
            BenchmarkId::new("Batch", &format!("DEPTH: {depth}")),
            &vec![(index, new_leaf)],
            |b, updates| b.iter(|| tree.batch_update(&updates)),
        );
    }
}

criterion_group! {
    name = merkle_tree;
    config = Criterion::default().sample_size(10);
    targets = new, append, update, batch_update, compare_single_leaf_update,
    // targets = compare_single_leaf_update,
}

criterion_main!(merkle_tree);
