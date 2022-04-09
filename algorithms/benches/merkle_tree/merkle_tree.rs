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

const NUM_WINDOWS: usize = 3;
const WINDOW_SIZE: usize = 57;
const TREE_DEPTH: usize = 32;

type H = BHPCRH<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE>;
type P = MerkleTreeParameters<H, TREE_DEPTH>;

const NUM_ENTRIES: &[usize] = &[10, 100, 1000, 10000];
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
    let parameters = P::setup(SETUP_MESSAGE);

    for entries in NUM_ENTRIES {
        let leaves = generate_random_leaves!(*entries, LEAF_SIZE);
        let mut merkle_tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), &[[0u8; LEAF_SIZE]]).unwrap();

        c.bench_function(&format!("New Merkle Tree ({} entries)", entries), move |b| {
            b.iter(|| {
                merkle_tree = merkle_tree.rebuild(1, &leaves).unwrap();
            })
        });
    }
}

fn insert(c: &mut Criterion) {
    let parameters = P::setup(SETUP_MESSAGE);

    for entries in NUM_ENTRIES {
        let leaves = generate_random_leaves!(*entries, LEAF_SIZE);
        let mut merkle_tree = MerkleTree::<P>::new(Arc::new(parameters.clone()), &[[0u8; LEAF_SIZE]]).unwrap();

        c.bench_function(&format!("Insert Merkle Tree ({} entries)", entries), move |b| {
            b.iter(|| {
                for (i, leaf) in leaves.iter().enumerate() {
                    merkle_tree = merkle_tree.rebuild(i + 1, &[leaf]).unwrap();
                }
            })
        });
    }
}

criterion_group! {
    name = merkle_tree_bhp;
    config = Criterion::default().sample_size(10);
    targets = new, insert
}

criterion_main!(merkle_tree_bhp);
