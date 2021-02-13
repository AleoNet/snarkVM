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

use snarkvm_algorithms::{
    crh::{BoweHopwoodPedersenCompressedCRH, PedersenSize},
    define_merkle_tree_parameters,
};
use snarkvm_curves::edwards_bls12::EdwardsProjective as EdwardsBls;
use snarkvm_utilities::ToBytes;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand;

pub const HASH_LENGTH: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Size;
impl PedersenSize for Size {
    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 32;
}

pub type MerkleTreeCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, Size>;

define_merkle_tree_parameters!(CommitmentMerkleParameters, MerkleTreeCRH, 32);

/// Generates a valid Merkle tree and verifies the Merkle path witness for each leaf.
fn generate_merkle_tree<P: LoadableMerkleParameters, L: ToBytes + Clone + Eq>(
    leaves: &[L],
    parameters: &P,
) -> MerkleTree<P> {
    MerkleTree::<P>::new(parameters.clone(), leaves).unwrap()
}

/// Emulates merkle tree inserts - The current implementation requires rebuilding the entire tree from the leaves.
fn insert<P: LoadableMerkleParameters, L: ToBytes + Clone + Eq>(parameters: P, mut _tree: MerkleTree<P>, leaves: &[L]) {
    for i in 1..leaves.len() {
        let _tree = generate_merkle_tree(&leaves[0..i], &parameters);
    }
}

/// Generate a random byte based on `rand::random`.
pub fn random_byte() -> u8 {
    rand::random::<u8>()
}

/// Generate random bytes of the given length.
pub fn random_bytes(n: usize) -> Vec<u8> {
    (0..n).map(|_| random_byte()).collect()
}

/// Generate a vector of random bytes with the given length.
pub fn random_hashes(n: usize) -> Vec<Vec<u8>> {
    (0..n).map(|_| random_bytes(HASH_LENGTH)).collect()
}

macro_rules! impl_bench_group {
    ($n:expr) => {
        paste::item_with_macros! {
            fn [<bench_group_ $n>](c: &mut Criterion) {
                let mut group = c.benchmark_group(format!("entry_num_{}", stringify!($n)));

                let leaves = random_hashes($n);

                impl_params_bench!(
                    {group, &leaves},
                    [insert,]
                );

                group.finish();
            }
        }
    };
}

macro_rules! impl_params_bench {
    ({$($g:tt)+}, [$f:tt, $($fn:tt),*]) => {
        impl_params_bench!({$($g)+}, [$f]);
        impl_params_bench!({$($g)+}, [$($fn),*]);
    };

    ({$($g:tt)+}, [$f:tt]) => {
        impl_bench_fn!({$($g)+}, $f);
    };

    ($($other:tt)*) => {};
}

macro_rules! impl_bench_fn {
    ({$g:ident, $l: expr}, $fn:ident) => {
        $g.bench_function(format!("{}", stringify!($fn)), |b| {
            let parameters = CommitmentMerkleParameters::default();
            let tree = generate_merkle_tree::<_, Vec<u8>>(&[], &parameters);

            b.iter(|| $fn(black_box(parameters.clone()), black_box(tree.clone()), black_box($l)))
        });
    };
}

impl_bench_group!(1);
impl_bench_group!(5);
impl_bench_group!(10);
impl_bench_group!(100);
impl_bench_group!(1000);
// impl_bench_group!(10000);

criterion_group!(
    benches,
    bench_group_1,
    bench_group_5,
    bench_group_10,
    bench_group_100,
    bench_group_1000,
    // bench_group_10000
);
criterion_main!(benches);
