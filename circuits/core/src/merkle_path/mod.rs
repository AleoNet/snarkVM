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

use crate::Poseidon;
use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::{Boolean, Field};

// TODO (raychu86): Remove use of `INPUT_SIZE_FE` as it is merely a requirement for
//  the `PoseidonCRH` implementation. Ideally merkle trees are updated to deal directly
//  with bits and field elements instead of bytes to prevent padding requirements.
pub struct MerklePath<E: Environment, const INPUT_SIZE_FE: usize> {
    // TODO (raychu86): Add support for generic hash functions.
    /// The Poseidon hash function.
    crh: Poseidon<E>,
    /// `traversal[i]` is 0 (false) iff ith node from bottom to top is left.
    traversal: Vec<Boolean<E>>,
    /// `path[i]` is the entry of sibling of ith node from bottom to top.
    path: Vec<Field<E>>,
}

impl<E: Environment, const INPUT_SIZE_FE: usize> Inject for MerklePath<E, INPUT_SIZE_FE> {
    type Primitive = (Vec<bool>, Vec<E::BaseField>);

    /// Initializes a merkle path from the given mode and `path`.
    fn new(mode: Mode, (traversal, path): Self::Primitive) -> MerklePath<E, INPUT_SIZE_FE> {
        let mut circuit_traversal = vec![];
        for position in traversal.iter() {
            circuit_traversal.push(Boolean::new(mode, *position));
        }

        let mut circuit_path = vec![];
        for node in path.iter() {
            circuit_path.push(Field::new(mode, *node));
        }

        Self { crh: Poseidon::new(), traversal: circuit_traversal, path: circuit_path }
    }
}

impl<E: Environment, const INPUT_SIZE_FE: usize> Eject for MerklePath<E, INPUT_SIZE_FE> {
    type Primitive = (Vec<bool>, Vec<E::BaseField>);

    ///
    /// Ejects the mode of the account private key.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.traversal, &self.path).eject_mode()
    }

    ///
    /// Ejects the account private key as `(sk_sig, r_sig)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.traversal, &self.path).eject_value()
    }
}

impl<E: Environment, const INPUT_SIZE_FE: usize> MerklePath<E, INPUT_SIZE_FE> {
    /// Calculate the root of the merkle tree given the leaf node.
    pub fn calculate_root(&self, leaf: Field<E>) -> Field<E> {
        let num_bits = E::BaseField::size_in_data_bits();
        let byte_size = num_bits + num_bits % 8;
        let input_size_bits: usize = INPUT_SIZE_FE * num_bits;

        // Pad the leaf according to the PoseidonCRH function.
        let mut leaf_bits = leaf.to_bits_le();
        leaf_bits.resize(byte_size, Boolean::new(Mode::Constant, false));

        let field_input: Vec<Field<E>> = leaf_bits.chunks(num_bits).map(Field::from_bits_le).collect();
        let mut curr_hash = self.crh.hash(&field_input);

        // To traverse up a MT, we iterate over the path from bottom to top

        // At any given bit, the bit being 0 indicates our currently hashed value is the left,
        // and the bit being 1 indicates our currently hashed value is on the right.
        // Thus `left_hash` is the sibling if bit is 1, and it's the computed hash if bit is 0
        for (bit, sibling) in self.traversal.iter().zip_eq(&self.path) {
            let left_hash = Field::ternary(bit, sibling, &curr_hash);
            let right_hash = Field::ternary(bit, &curr_hash, sibling);

            // TODO (raychu86) Avoid this by using the Fields as input.
            let mut left_hash_bits = left_hash.to_bits_le();
            let mut right_hash_bits = right_hash.to_bits_le();

            // Pad the bits to the input size according to the native PoseidonCRH function.
            let input_field_elements: Vec<Field<E>> = {
                left_hash_bits.resize(byte_size, Boolean::new(Mode::Constant, false));
                right_hash_bits.resize(byte_size, Boolean::new(Mode::Constant, false));

                let mut input_bits: Vec<Boolean<E>> = [left_hash_bits, right_hash_bits].concat();
                assert!(input_bits.len() <= input_size_bits, "PoseidonCRH input bits exceeds supported input size");

                if input_bits.len() < input_size_bits {
                    input_bits.resize(input_size_bits, Boolean::new(Mode::Constant, false));
                }

                input_bits.chunks(num_bits).map(Field::from_bits_le).collect()
            };

            curr_hash = self.crh.hash(&input_field_elements);
        }

        curr_hash
    }

    // TODO (raychu86): Ideally use the following implementation without bit padding.
    // pub fn calculate_root(&self, leaf: Field<E>) -> Field<E> {
    //     let mut curr_hash = self.crh.hash(&[leaf]);
    //
    //     // To traverse up a MT, we iterate over the path from bottom to top
    //
    //     // At any given bit, the bit being 0 indicates our currently hashed value is the left,
    //     // and the bit being 1 indicates our currently hashed value is on the right.
    //     // Thus `left_hash` is the sibling if bit is 1, and it's the computed hash if bit is 0
    //     for (bit, sibling) in self.traversal.iter().zip_eq(&self.path) {
    //         let left_hash = Field::ternary(bit, sibling, &curr_hash);
    //         let right_hash = Field::ternary(bit, &curr_hash, sibling);
    //
    //         curr_hash = self.crh.hash(&[left_hash, right_hash]);
    //     }
    //
    //     curr_hash
    // }

    pub fn verify(&self, leaf: Field<E>, root: Field<E>) {
        let expected_root = self.calculate_root(leaf);
        E::assert_eq(&expected_root, &root);
    }

    pub fn conditionally_verify(&self, leaf: Field<E>, root: Field<E>, condition: Boolean<E>) {
        let expected_root = self.calculate_root(leaf);
        let is_equal = expected_root.is_equal(&root);

        // TODO (raychu86): Consider adding a conditional_assert_eq function.
        // If `condition` is true, we check that the root is equal to the expected root,
        // however if `condition` is false, we trivially check that `false` is equal to `false`.
        let final_condition = &condition & is_equal;
        E::assert_eq(&condition, &final_condition);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{
        crh::PoseidonCRH as NativePoseidon,
        merkle_tree::{MaskedMerkleTreeParameters, MerkleTree},
        traits::MerkleParameters,
    };
    use snarkvm_circuits_environment::{assert_scope, Circuit, Mode};
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::sync::Arc;

    const INPUT_SIZE_FE: usize = 3;
    const TREE_DEPTH: usize = 4;

    type H = NativePoseidon<Fr, INPUT_SIZE_FE>;
    type EdwardsMerkleParameters = MaskedMerkleTreeParameters<H, TREE_DEPTH>;

    fn check_merkle_path(
        mode: Mode,
        use_bad_root: bool,
        num_inputs: usize,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let native_hasher = EdwardsMerkleParameters::setup("Poseidon merkle path test");

        let mut rng = test_rng();
        let mut leaves = Vec::new();
        for _ in 0..1 << EdwardsMerkleParameters::DEPTH {
            leaves.push(Fr::rand(&mut rng));
        }

        let merkle_tree = MerkleTree::new(Arc::new(native_hasher), &leaves).unwrap();
        let root = merkle_tree.root();
        let bad_root = Fr::zero();

        for (i, leaf) in leaves.iter().enumerate() {
            let proof = merkle_tree.generate_proof(i, &leaf).unwrap();
            assert!(proof.verify(root, &leaf).unwrap());

            let root = if use_bad_root { &bad_root } else { root };

            Circuit::scope(format!("Poseidon {mode} merkle tree {i}"), || {
                let traversal = proof.position_list().collect::<Vec<_>>();
                let path = proof.path.clone();
                let merkle_path = MerklePath::<Circuit, INPUT_SIZE_FE>::new(mode, (traversal, path));

                let circuit_leaf = Field::new(mode, *leaf);
                let circuit_root = Field::new(mode, *root);

                assert_eq!(circuit_leaf.eject_value(), *leaf);

                merkle_path.verify(circuit_leaf, circuit_root);

                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn good_root_test_constant() {
        check_merkle_path(Mode::Constant, false, 0, 2774, 0, 0, 0);
    }

    #[test]
    fn good_root_test_public() {
        check_merkle_path(Mode::Public, false, 0, 487, 10, 4005, 4019);
    }

    #[test]
    fn good_root_test_private() {
        check_merkle_path(Mode::Private, false, 0, 487, 0, 4015, 4019);
    }

    #[should_panic]
    #[test]
    fn bad_root_test_constant() {
        check_merkle_path(Mode::Constant, true, 0, 2774, 0, 0, 0);
    }

    #[should_panic]
    #[test]
    fn bad_root_test_public() {
        check_merkle_path(Mode::Public, true, 0, 487, 10, 4005, 4019);
    }

    #[should_panic]
    #[test]
    fn bad_root_test_private() {
        check_merkle_path(Mode::Private, true, 0, 487, 0, 4015, 4019);
    }
}
