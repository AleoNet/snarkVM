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

use std::sync::Arc;

use rand::{thread_rng, Rng};

use snarkvm_algorithms::{
    crypto_hash::PoseidonCryptoHash,
    define_merkle_trie_parameters,
    merkle_trie::MerkleTrie,
    traits::{MerkleTrieParameters, CRH},
};
use snarkvm_curves::bls12_377::Fr;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::ToBytes;

use crate::{
    algorithms::merkle_trie::*,
    integers::uint::UInt8,
    traits::{algorithms::CRHGadget, alloc::AllocGadget},
};

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

fn generate_merkle_tree<
    P: MerkleTrieParameters,
    F: PrimeField,
    HG: CRHGadget<P::H, F>,
    L: ToBytes + Send + Sync + Clone + Eq,
>(
    key_pairs: Vec<(Vec<u8>, L)>,
    use_bad_root: bool,
) {
    let parameters = P::setup("merkle_trie_test");
    let trie = MerkleTrie::<P, _>::new(Arc::new(parameters.clone()), key_pairs.clone()).unwrap();
    let root = trie.root();
    let mut satisfied = true;
    for (i, (key, value)) in key_pairs.iter().enumerate() {
        let mut cs = TestConstraintSystem::<F>::new();
        let proof = trie.generate_proof(key, value).unwrap();
        assert!(proof.verify(&root, &key, value).unwrap());

        // Allocate Merkle tree root
        let root = <HG as CRHGadget<_, _>>::OutputGadget::alloc(&mut cs.ns(|| format!("new_digest_{}", i)), || {
            if use_bad_root {
                Ok(<P::H as CRH>::Output::default())
            } else {
                Ok(root.clone())
            }
        })
        .unwrap();

        let constraints_from_digest = cs.num_constraints();
        println!("constraints from digest: {}", constraints_from_digest);

        // Allocate CRH
        let crh_parameters = HG::alloc_constant(&mut cs.ns(|| format!("new_parameters_{}", i)), || {
            Ok(parameters.crh().clone())
        })
        .unwrap();

        let constraints_from_parameters = cs.num_constraints() - constraints_from_digest;
        println!("constraints from parameters: {}", constraints_from_parameters);

        // Allocate key
        let key = UInt8::constant_vec(&key);

        let constraints_from_key = cs.num_constraints() - constraints_from_parameters - constraints_from_digest;
        println!("constraints from key: {}", constraints_from_key);

        // Allocate value
        let value = UInt8::constant_vec(&value.to_bytes_le().unwrap());

        let constraints_from_value =
            cs.num_constraints() - constraints_from_parameters - constraints_from_digest - constraints_from_key;
        println!("constraints from value: {}", constraints_from_value);

        // Allocate Merkle tree path
        let cw =
            MerkleTriePathGadget::<_, HG, _>::alloc(&mut cs.ns(|| format!("new_witness_{}", i)), || Ok(proof)).unwrap();

        let constraints_from_path = cs.num_constraints()
            - constraints_from_parameters
            - constraints_from_digest
            - constraints_from_key
            - constraints_from_value;
        println!("constraints from path: {}", constraints_from_path);
        cw.check_membership(
            &mut cs.ns(|| format!("new_witness_check_{}", i)),
            &crh_parameters,
            &root,
            &key,
            &value,
        )
        .unwrap();
        if !cs.is_satisfied() {
            satisfied = false;
            println!("Unsatisfied constraint: {}", cs.which_is_unsatisfied().unwrap());
        }
        let setup_constraints = constraints_from_key
            + constraints_from_value
            + constraints_from_digest
            + constraints_from_parameters
            + constraints_from_path;
        println!("number of constraints: {}", cs.num_constraints() - setup_constraints);
    }

    assert!(satisfied);
}

mod merkle_trie_poseidon {
    use super::*;
    use crate::algorithms::crypto_hash::PoseidonCryptoHashGadget;

    type H = PoseidonCryptoHash<Fr, 4, false>;
    type HG = PoseidonCryptoHashGadget<Fr, 4, false>;

    const KEY_SIZE: usize = 32;
    const VALUE_SIZE: usize = 32;

    #[test]
    fn good_root_test() {
        define_merkle_trie_parameters!(MerkleTrieParams, H, 16, 32, KEY_SIZE, VALUE_SIZE);

        let key_pairs = generate_random_key_pairs!(4, KEY_SIZE, VALUE_SIZE);

        generate_merkle_tree::<MerkleTrieParams, Fr, HG, _>(key_pairs, false);
    }

    #[should_panic]
    #[test]
    fn bad_root_test() {
        define_merkle_trie_parameters!(MerkleTrieParams, H, 16, 32, KEY_SIZE, VALUE_SIZE);

        let key_pairs = generate_random_key_pairs!(4, KEY_SIZE, VALUE_SIZE);

        generate_merkle_tree::<MerkleTrieParams, Fr, HG, _>(key_pairs, true);
    }
}
