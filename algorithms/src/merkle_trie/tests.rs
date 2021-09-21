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

#[cfg(test)]
mod tests {
    use crate::{crypto_hash::PoseidonCryptoHash, merkle_trie::MerkleTrie, traits::CRH};

    use snarkvm_curves::bls12_377::Fr;

    use std::sync::Arc;

    type H = PoseidonCryptoHash<Fr, 4, false>;

    const VALUE_PAIR_1: (&'static [u8; 1], u8) = (b"a", 1u8);
    const VALUE_PAIR_2: (&'static [u8; 2], u8) = (b"ab", 2u8);
    const VALUE_PAIR_3: (&'static [u8; 3], u8) = (b"abc", 3u8);
    const VALUE_PAIR_4: (&'static [u8; 4], u8) = (b"abcd", 4u8);

    #[test]
    fn test_basic_trie() {
        let crh = Arc::new(H::setup("TEST_MERKLE_TRIE_CRH"));

        let mut tree_1 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_1.insert(VALUE_PAIR_1.0, Some(VALUE_PAIR_1.1)).unwrap();
        tree_1.insert(VALUE_PAIR_2.0, Some(VALUE_PAIR_2.1)).unwrap();
        tree_1.insert(VALUE_PAIR_3.0, Some(VALUE_PAIR_3.1)).unwrap();

        let mut tree_2 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_2.insert(VALUE_PAIR_1.0, Some(VALUE_PAIR_1.1)).unwrap();
        tree_2.insert(VALUE_PAIR_2.0, Some(VALUE_PAIR_2.1)).unwrap();
        tree_2.insert(VALUE_PAIR_3.0, Some(VALUE_PAIR_3.1)).unwrap();

        assert_eq!(&tree_1.root(), &tree_2.root());
    }

    #[test]
    fn test_basic_mismatched_trie() {
        let crh = Arc::new(H::setup("TEST_MERKLE_TRIE_CRH"));

        let mut tree_1 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_1.insert(VALUE_PAIR_1.0, Some(VALUE_PAIR_1.1)).unwrap();
        tree_1.insert(VALUE_PAIR_2.0, Some(VALUE_PAIR_2.1)).unwrap();
        tree_1.insert(VALUE_PAIR_3.0, Some(VALUE_PAIR_3.1)).unwrap();

        let mut tree_2 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_2.insert(VALUE_PAIR_1.0, Some(VALUE_PAIR_1.1)).unwrap();
        tree_2.insert(VALUE_PAIR_2.0, Some(VALUE_PAIR_2.1)).unwrap();
        tree_2.insert(VALUE_PAIR_4.0, Some(VALUE_PAIR_4.1)).unwrap();

        assert_ne!(&tree_1.root(), &tree_2.root());
    }

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
