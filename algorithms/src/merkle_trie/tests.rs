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

use crate::{
    crypto_hash::PoseidonCryptoHash,
    define_merkle_trie_parameters,
    merkle_trie::{MerkleTrie, MerkleTrieDigest},
    traits::{MerkleTrieParameters, CRH},
};
use snarkvm_utilities::ToBytes;

use rand::{thread_rng, Rng};
use std::sync::Arc;

/// Generates the specified number of random Merkle trie key_pairs.
macro_rules! generate_random_key_pairs {
    ($num_leaves:expr, $key_size:expr, $leaf_size:expr) => {{
        let mut rng = thread_rng();

        let mut key_pairs = Vec::with_capacity($num_leaves);
        for _ in 0..$num_leaves {
            let mut key = [0u8; $key_size];
            rng.fill(&mut key);

            let mut val = [0u8; $leaf_size];
            rng.fill(&mut val);

            key_pairs.push((key.to_vec(), val));
        }

        key_pairs
    }};
}

/// Generates a valid Merkle trie and verifies the Merkle path witness for each leaf.
fn generate_merkle_trie<P: MerkleTrieParameters, L: ToBytes + Send + Sync + Clone + Eq>(
    key_pairs: Vec<(Vec<u8>, L)>,
    parameters: &P,
) -> MerkleTrie<P, L> {
    let trie = MerkleTrie::<P, L>::new(Arc::new(parameters.clone()), key_pairs.clone()).unwrap();
    for (_, (key, leaf)) in key_pairs.iter().enumerate() {
        let proof = trie.generate_proof(&key, &leaf).unwrap();
        assert!(proof.verify(&trie.root(), &key, &leaf).unwrap());
    }
    trie
}

/// Generates a valid Merkle trie and gets/removes each pair.
fn generate_merkle_trie_get_and_remove<P: MerkleTrieParameters, L: ToBytes + Send + Sync + Clone + Eq>(
    key_pairs: Vec<(Vec<u8>, L)>,
    parameters: &P,
) -> MerkleTrie<P, L> {
    let mut trie = MerkleTrie::<P, L>::new(Arc::new(parameters.clone()), key_pairs.clone()).unwrap();
    for (_, (key, leaf)) in key_pairs.iter().enumerate() {
        let value_bytes = trie.get(&key).unwrap().to_bytes_le().unwrap();
        assert_eq!(&value_bytes, &leaf.to_bytes_le().unwrap());
        let removed = trie.remove(&key).unwrap().unwrap();
        assert_eq!(&value_bytes, &removed.to_bytes_le().unwrap());
        assert!(trie.get(&key).is_none());
    }
    trie
}

/// Generates a valid Merkle trie and verifies the Merkle path witness for each leaf does not verify to an invalid root hash.
fn bad_merkle_trie_verify<P: MerkleTrieParameters, L: ToBytes + Send + Sync + Clone + Eq>(
    key_pairs: Vec<(Vec<u8>, L)>,
    parameters: &P,
) -> MerkleTrie<P, L> {
    let bad_root = MerkleTrieDigest::<P>::default();
    let trie = MerkleTrie::<P, L>::new(Arc::new(parameters.clone()), key_pairs.clone()).unwrap();
    for (_, (key, leaf)) in key_pairs.iter().enumerate() {
        let proof = trie.generate_proof(&key, &leaf).unwrap();
        assert!(proof.verify(&bad_root, &key, &leaf).unwrap());
    }
    trie
}

fn run_empty_merkle_trie_test<P: MerkleTrieParameters>() {
    let parameters = &P::setup("merkle_trie_test");
    generate_merkle_trie::<P, Vec<u8>>(vec![], parameters);
}

fn run_good_root_test<P: MerkleTrieParameters>() {
    let parameters = &P::setup("merkle_trie_test");

    const KEY_SIZE: usize = 32;
    const VALUE_SIZE: usize = 32;
    assert_eq!(P::KEY_SIZE, KEY_SIZE);
    assert_eq!(P::VALUE_SIZE, VALUE_SIZE);

    let key_pairs = generate_random_key_pairs!(4, KEY_SIZE, VALUE_SIZE);
    generate_merkle_trie::<P, _>(key_pairs, parameters);

    let key_pairs = generate_random_key_pairs!(16, KEY_SIZE, VALUE_SIZE);
    generate_merkle_trie::<P, _>(key_pairs, parameters);
}

fn run_bad_root_test<P: MerkleTrieParameters>() {
    let parameters = &P::setup("merkle_trie_test");

    const KEY_SIZE: usize = 32;
    const VALUE_SIZE: usize = 32;
    assert_eq!(P::KEY_SIZE, KEY_SIZE);
    assert_eq!(P::VALUE_SIZE, VALUE_SIZE);

    let key_pairs = generate_random_key_pairs!(4, KEY_SIZE, VALUE_SIZE);
    generate_merkle_trie::<P, _>(key_pairs, parameters);

    let key_pairs = generate_random_key_pairs!(16, KEY_SIZE, VALUE_SIZE);
    bad_merkle_trie_verify::<P, _>(key_pairs, parameters);
}

fn run_get_remove_test<P: MerkleTrieParameters>() {
    let parameters = &P::setup("merkle_trie_test");

    const KEY_SIZE: usize = 32;
    const VALUE_SIZE: usize = 32;
    assert_eq!(P::KEY_SIZE, KEY_SIZE);
    assert_eq!(P::VALUE_SIZE, VALUE_SIZE);

    let key_pairs = generate_random_key_pairs!(4, KEY_SIZE, VALUE_SIZE);
    generate_merkle_trie_get_and_remove::<P, _>(key_pairs, parameters);

    let key_pairs = generate_random_key_pairs!(16, KEY_SIZE, VALUE_SIZE);
    generate_merkle_trie_get_and_remove::<P, _>(key_pairs, parameters);
}

mod poseidon_on_bls12_377_fr {
    use super::*;
    use snarkvm_curves::bls12_377::Fr;

    #[test]
    fn empty_merkle_trie_test() {
        define_merkle_trie_parameters!(MerkleTrieParams, PoseidonCryptoHash<Fr, 4, false>, 64, 32, 32);

        run_empty_merkle_trie_test::<MerkleTrieParams>();
    }

    #[test]
    fn merkle_trie_get_remove_test() {
        define_merkle_trie_parameters!(MerkleTrieParams, PoseidonCryptoHash<Fr, 4, false>, 64, 32, 32);

        run_get_remove_test::<MerkleTrieParams>();
    }

    #[test]
    fn good_root_test() {
        define_merkle_trie_parameters!(MerkleTrieParams, PoseidonCryptoHash<Fr, 4, false>, 64, 32, 32);

        run_good_root_test::<MerkleTrieParams>();
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        define_merkle_trie_parameters!(MerkleTrieParams, PoseidonCryptoHash<Fr, 4, false>, 64, 32, 32);

        run_bad_root_test::<MerkleTrieParams>();
    }

    const VALUE_PAIR_1: (&'static [u8; 1], u8) = (b"a", 1u8);
    const VALUE_PAIR_2: (&'static [u8; 1], u8) = (b"b", 2u8);
    const VALUE_PAIR_3: (&'static [u8; 1], u8) = (b"c", 3u8);
    const VALUE_PAIR_4: (&'static [u8; 1], u8) = (b"d", 4u8);

    #[test]
    fn test_trie_get() {
        define_merkle_trie_parameters!(MerkleTrieParams, PoseidonCryptoHash<Fr, 4, false>, 64, 1, 1);

        let crh = Arc::new(MerkleTrieParams::setup("TEST_MERKLE_TRIE_CRH"));

        let mut trie_1 = MerkleTrie::<_, u8>::new(crh.clone(), vec![]).unwrap();

        trie_1.insert(VALUE_PAIR_1.0, VALUE_PAIR_1.1).unwrap();
        trie_1.insert(VALUE_PAIR_2.0, VALUE_PAIR_2.1).unwrap();
        trie_1.insert(VALUE_PAIR_3.0, VALUE_PAIR_3.1).unwrap();

        let value_1 = trie_1.get(VALUE_PAIR_1.0);
        let value_2 = trie_1.get(VALUE_PAIR_2.0);
        let value_3 = trie_1.get(VALUE_PAIR_3.0);
        let value_4 = trie_1.get(VALUE_PAIR_4.0);

        assert_eq!(value_1, Some(&VALUE_PAIR_1.1));
        assert_eq!(value_2, Some(&VALUE_PAIR_2.1));
        assert_eq!(value_3, Some(&VALUE_PAIR_3.1));
        assert_eq!(value_4, None);
    }

    #[test]
    fn test_trie_verify() {
        define_merkle_trie_parameters!(MerkleTrieParams, PoseidonCryptoHash<Fr, 4, false>, 64, 1, 1);

        let crh = Arc::new(MerkleTrieParams::setup("TEST_MERKLE_TRIE_CRH"));

        let mut trie_1 = MerkleTrie::<_, u8>::new(crh.clone(), vec![]).unwrap();

        trie_1.insert(VALUE_PAIR_1.0, VALUE_PAIR_1.1).unwrap();
        trie_1.insert(VALUE_PAIR_2.0, VALUE_PAIR_2.1).unwrap();
        trie_1.insert(VALUE_PAIR_3.0, VALUE_PAIR_3.1).unwrap();

        let proof = trie_1.generate_proof(VALUE_PAIR_3.0, &VALUE_PAIR_3.1).unwrap();

        assert!(proof.verify(&trie_1.root(), VALUE_PAIR_3.0, &VALUE_PAIR_3.1).unwrap());
    }
}
