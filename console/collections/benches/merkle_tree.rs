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

#[macro_use]
extern crate criterion;

use snarkvm_console_network::{
    prelude::{test_rng, ToBits, Uniform},
    Network,
    Testnet3,
};
use snarkvm_console_types::Field;

use criterion::Criterion;

const DEPTH: u8 = 32;

// const NUM_LEAVES: &[usize] = &[10, 100, 200, 500, 1000, 10000];
const NUM_LEAVES: &[usize] = &[10, 100, 1000, 10000];
const APPEND_SIZES: &[usize] = &[10, 100, 1000];

/// Generates the specified number of random Merkle tree leaves.
macro_rules! generate_leaves {
    ($num_leaves:expr) => {{ (0..$num_leaves).map(|_| Field::<Testnet3>::rand(&mut test_rng()).to_bits_le()).collect::<Vec<_>>() }};
}

fn new(c: &mut Criterion) {
    for num_leaves in NUM_LEAVES {
        let leaves = generate_leaves!(*num_leaves);

        c.bench_function(&format!("MerkleTree::new ({} leaves)", num_leaves), move |b| {
            b.iter(|| {
                let _tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
            })
        });
    }
}

fn append(c: &mut Criterion) {
    for num_leaves in NUM_LEAVES {
        let leaves = generate_leaves!(*num_leaves);

        let merkle_tree = Testnet3::merkle_tree_bhp::<DEPTH>(&leaves).unwrap();
        let new_leaf = generate_leaves!(1);

        c.bench_function(
            &format!("MerkleTree::append (adding single leaf to a tree with {} leaves)", num_leaves),
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
            let new_leaves = generate_leaves!(*num_new_leaves);

            c.bench_function(
                &format!(
                    "MerkleTree::append (adding {} new leaves to a tree with {} leaves)",
                    num_new_leaves, num_leaves
                ),
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

criterion_group! {
    name = merkle_tree;
    config = Criterion::default().sample_size(10);
    targets = new, append
}

criterion_main!(merkle_tree);
