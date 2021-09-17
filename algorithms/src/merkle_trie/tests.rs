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

    #[test]
    fn test_basic_trie() {
        let crh = Arc::new(H::setup("TEST_MERKLE_TRIE_CRH"));

        let mut tree_1 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_1.insert(b"a", Some(1)).unwrap();
        tree_1.insert(b"ab", Some(2)).unwrap();
        tree_1.insert(b"abc", Some(3)).unwrap();

        let mut tree_2 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_2.insert(b"a", Some(1)).unwrap();
        tree_2.insert(b"ab", Some(2)).unwrap();
        tree_2.insert(b"abc", Some(3)).unwrap();

        assert_eq!(&tree_1.root(), &tree_2.root());
    }

    #[test]
    fn test_basic_mismatched_trie() {
        let crh = Arc::new(H::setup("TEST_MERKLE_TRIE_CRH"));

        let mut tree_1 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_1.insert(b"a", Some(1)).unwrap();
        tree_1.insert(b"ab", Some(2)).unwrap();
        tree_1.insert(b"abc", Some(3)).unwrap();

        let mut tree_2 = MerkleTrie::<_, u8>::new(crh.clone()).unwrap();
        tree_2.insert(b"a", Some(1)).unwrap();
        tree_2.insert(b"aa", Some(2)).unwrap();
        tree_2.insert(b"abb", Some(3)).unwrap();

        assert_ne!(&tree_1.root(), &tree_2.root());
    }
}
