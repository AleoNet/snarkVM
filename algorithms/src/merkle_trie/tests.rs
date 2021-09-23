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

use crate::{crypto_hash::PoseidonCryptoHash, merkle_trie::MerkleTrie, traits::CRH};
use snarkvm_utilities::ToBytes;

use rand::{thread_rng, Rng};
use std::sync::Arc;

/// Generates the specified number of random Merkle trie key_pairs.
macro_rules! generate_random_key_pairs {
    ($num_leaves:expr, $key_size:expr, $leaf_size:expr) => {{
        let mut rng = thread_rng();

        let mut keys = Vec::with_capacity($num_leaves);
        for _ in 0..$num_leaves {
            let mut id = [0u8; $key_size];
            rng.fill(&mut id);
            keys.push(id.to_vec());
        }

        let mut leaves = Vec::with_capacity($num_leaves);
        for _ in 0..$num_leaves {
            let mut id = [0u8; $leaf_size];
            rng.fill(&mut id);
            leaves.push(id);
        }

        (keys, leaves)
    }};
}

/// Generates a valid Merkle trie and verifies the Merkle path witness for each leaf.
fn generate_merkle_trie<P: CRH, L: std::fmt::Debug + ToBytes + Send + Sync + Clone + Eq>(
    keys: &[Vec<u8>],
    leaves: &[L],
    parameters: &P,
) -> MerkleTrie<P, L> {
    let mut trie = MerkleTrie::<P, L>::new(Arc::new(parameters.clone())).unwrap();
    for (_, (key, leaf)) in keys.iter().zip(leaves.iter()).enumerate() {
        trie.insert(&key, Some(leaf.clone())).unwrap();
        let proof = trie.generate_proof(&key, &leaf).unwrap();
        assert!(proof.verify(&trie.root(), &key, &leaf).unwrap());
    }
    trie
}

/// Generates a valid Merkle trie and verifies the Merkle path witness for each leaf does not verify to an invalid root hash.
fn bad_merkle_trie_verify<P: CRH, L: ToBytes + Send + Sync + Clone + Eq>(
    keys: &[Vec<u8>],
    leaves: &[L],
    parameters: &P,
) -> MerkleTrie<P, L> {
    let bad_root = [0u8; 32];
    let mut trie = MerkleTrie::<P, L>::new(Arc::new(parameters.clone())).unwrap();
    for (_, (key, leaf)) in keys.iter().zip(leaves.iter()).enumerate() {
        trie.insert(&key, Some(leaf.clone())).unwrap();
        let proof = trie.generate_proof(&key, &leaf).unwrap();
        assert!(proof.verify(&bad_root, &key, &leaf).unwrap());
    }
    trie
}

fn run_empty_merkle_tree_test<P: CRH>() {
    let parameters = &P::setup("merkle_trie_test");
    generate_merkle_trie::<P, Vec<u8>>(&[], &[], parameters);
}

fn run_good_root_test<P: CRH>() {
    let parameters = &P::setup("merkle_trie_test");

    let (keys, leaves) = generate_random_key_pairs!(4, 32, 32);
    generate_merkle_trie::<P, _>(&keys, &leaves, parameters);

    let (keys, leaves) = generate_random_key_pairs!(16, 32, 32);
    generate_merkle_trie::<P, _>(&keys, &leaves, parameters);
}

fn run_bad_root_test<P: CRH>() {
    let parameters = &P::setup("merkle_tree_test");

    let (keys, leaves) = generate_random_key_pairs!(4, 32, 32);
    generate_merkle_trie::<P, _>(&keys, &leaves, parameters);

    let (keys, leaves) = generate_random_key_pairs!(16, 32, 32);
    bad_merkle_trie_verify::<P, _>(&keys, &leaves, parameters);
}

mod poseidon_on_bls12_377_fr {
    use super::*;
    use snarkvm_curves::bls12_377::Fr;

    type H = PoseidonCryptoHash<Fr, 4, false>;

    #[test]
    fn empty_merkle_tree_test() {
        run_empty_merkle_tree_test::<H>();
    }

    #[test]
    fn good_root_test_123() {
        run_good_root_test::<H>();
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        run_bad_root_test::<H>();
    }

    const VALUE_PAIR_1: (&'static [u8; 1], u8) = (b"a", 1u8);
    const VALUE_PAIR_2: (&'static [u8; 2], u8) = (b"ab", 2u8);
    const VALUE_PAIR_3: (&'static [u8; 3], u8) = (b"abc", 3u8);
    const VALUE_PAIR_4: (&'static [u8; 4], u8) = (b"abcd", 4u8);

    #[test]
    fn test_trie_get() {
        let crh = Arc::new(H::setup("TEST_MERKLE_TRIE_CRH"));

        let mut tree_1 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();

        tree_1.insert(VALUE_PAIR_1.0, Some(VALUE_PAIR_1.1)).unwrap();
        tree_1.insert(VALUE_PAIR_2.0, Some(VALUE_PAIR_2.1)).unwrap();
        tree_1.insert(VALUE_PAIR_3.0, Some(VALUE_PAIR_3.1)).unwrap();

        let value_1 = tree_1.get(VALUE_PAIR_1.0);
        let value_2 = tree_1.get(VALUE_PAIR_2.0);
        let value_3 = tree_1.get(VALUE_PAIR_3.0);
        let value_4 = tree_1.get(VALUE_PAIR_4.0);

        assert_eq!(value_1, Some(&VALUE_PAIR_1.1));
        assert_eq!(value_2, Some(&VALUE_PAIR_2.1));
        assert_eq!(value_3, Some(&VALUE_PAIR_3.1));
        assert_eq!(value_4, None);
    }

    #[test]
    fn test_trie_verify() {
        let crh = Arc::new(H::setup("TEST_MERKLE_TRIE_CRH"));

        let mut tree_1 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();

        tree_1.insert(VALUE_PAIR_1.0, Some(VALUE_PAIR_1.1)).unwrap();
        tree_1.insert(VALUE_PAIR_2.0, Some(VALUE_PAIR_2.1)).unwrap();
        tree_1.insert(VALUE_PAIR_3.0, Some(VALUE_PAIR_3.1)).unwrap();

        let proof = tree_1.generate_proof(VALUE_PAIR_3.0, &VALUE_PAIR_3.1).unwrap();

        assert!(proof.verify(&tree_1.root(), VALUE_PAIR_3.0, &VALUE_PAIR_3.1).unwrap());
    }
}
