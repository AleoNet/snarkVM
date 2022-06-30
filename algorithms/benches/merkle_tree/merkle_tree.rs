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

use snarkvm_algorithms::{
    crh::BHPCRH,
    merkle_tree::{MerkleTree, MerkleTreeParameters},
    traits::MerkleParameters,
};
use snarkvm_curves::edwards_bls12::EdwardsProjective;

use rand::{thread_rng, Rng};
use std::sync::Arc;

use criterion::Criterion;

const SETUP_MESSAGE: &str = "merkle_tree_bhp_benchmark";

const TREE_DEPTH: usize = 32;

type LeafCRH = BHPCRH<EdwardsProjective, 8, 54>;
type TwoToOneCRH = BHPCRH<EdwardsProjective, 6, 43>;
type P = MerkleTreeParameters<LeafCRH, TwoToOneCRH, TREE_DEPTH>;

const NUM_ENTRIES: &[usize] = &[10, 100, 1000, 10000];
const REBUILD_SIZES: &[usize] = &[10, 100, 1000];
const LEAF_SIZE: usize = 32;

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

fn new(c: &mut Criterion) {
    for entries in NUM_ENTRIES {
        let parameters = Arc::new(P::setup(SETUP_MESSAGE));
        let leaves = generate_random_leaves!(*entries, LEAF_SIZE);

        c.bench_function(&format!("New Merkle Tree ({} entries)", entries), move |b| {
            b.iter(|| {
                MerkleTree::<P>::new(parameters.clone(), &leaves).unwrap();
            })
        });
    }
}

fn rebuild_single_leaf(c: &mut Criterion) {
    let parameters = Arc::new(P::setup(SETUP_MESSAGE));

    for entries in NUM_ENTRIES {
        let leaves = generate_random_leaves!(*entries, LEAF_SIZE);
        let num_leaves = leaves.len();
        let mut merkle_tree = MerkleTree::<P>::new(parameters.clone(), &leaves).unwrap();
        let new_leaf = generate_random_leaves!(1, LEAF_SIZE)[0];

        c.bench_function(
            &format!("Rebuild Merkle Tree (add single leaf to a tree with {} leaves)", entries),
            move |b| {
                b.iter(|| {
                    merkle_tree = merkle_tree.rebuild(num_leaves, &[new_leaf]).unwrap();
                })
            },
        );
    }
}

fn rebuild_multiple_leaves(c: &mut Criterion) {
    let parameters = Arc::new(P::setup(SETUP_MESSAGE));

    for entries in NUM_ENTRIES {
        for num_new_leaves in REBUILD_SIZES {
            let leaves = generate_random_leaves!(*entries, LEAF_SIZE);
            let num_leaves = leaves.len();
            let mut merkle_tree = MerkleTree::<P>::new(parameters.clone(), &leaves).unwrap();

            let new_leaves = generate_random_leaves!(*num_new_leaves, LEAF_SIZE);

            c.bench_function(
                &format!("Rebuild Merkle Tree (add {} new leaves to a tree with {} leaves)", num_new_leaves, entries),
                move |b| {
                    b.iter(|| {
                        merkle_tree = merkle_tree.rebuild(num_leaves, &new_leaves).unwrap();
                    })
                },
            );
        }
    }
}

criterion_group! {
    name = merkle_tree;
    config = Criterion::default().sample_size(10);
    targets = new, rebuild_single_leaf, rebuild_multiple_leaves
}

criterion_main!(merkle_tree);
