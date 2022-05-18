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

use super::*;

impl<E: Environment, TwoToOneCRH: Hash> MerklePath<E, TwoToOneCRH> {
    pub fn to_root<LeafCRH: Hash<Output = TwoToOneCRH::Output>>(
        &self,
        leaf_crh: &LeafCRH,
        two_to_one_crh: &TwoToOneCRH,
        leaf: &[LeafCRH::Input],
    ) -> TwoToOneCRH::Output
    where
        <<TwoToOneCRH as Hash>::Output as Ternary>::Boolean: From<Boolean<E>>,
        Vec<<TwoToOneCRH as Hash>::Input>: From<Vec<<<TwoToOneCRH as Hash>::Output as ToBits>::Boolean>>,
    {
        let mut curr_hash = leaf_crh.hash(leaf);

        // Padding used to match the native merkle tree.
        let padding = TwoToOneCRH::Input::blank(Mode::Constant);

        // To traverse up a MT, we iterate over the path from bottom to top

        // At any given bit, the bit being 0 indicates our currently hashed value is the left,
        // and the bit being 1 indicates our currently hashed value is on the right.
        // Thus `left_hash` is the sibling if bit is 1, and it's the computed hash if bit is 0.
        for (bit, sibling) in self.traversal.iter().zip_eq(&self.path) {
            let left_hash: TwoToOneCRH::Output = Ternary::ternary(&bit.clone().into(), sibling, &curr_hash);
            let right_hash: TwoToOneCRH::Output = Ternary::ternary(&bit.clone().into(), &curr_hash, sibling);

            let mut left_input: Vec<TwoToOneCRH::Input> = left_hash.to_bits_le().into();
            let mut right_input: Vec<TwoToOneCRH::Input> = right_hash.to_bits_le().into();

            // Pad the inputs to the closest factor of 8 (byte representation). This is required due to the
            // native merkle tree hashing implementation.
            let num_bytes = ((left_input.len() + 7) / 8) * 8;
            left_input.resize(num_bytes, padding.clone());
            right_input.resize(num_bytes, padding.clone());

            curr_hash = two_to_one_crh.hash(&[left_input, right_input].concat());
        }

        curr_hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::Pedersen;

    use snarkvm_algorithms::{
        crh::PedersenCompressedCRH as NativePedersenCompressed,
        merkle_tree::{MaskedMerkleTreeParameters, MerkleTree},
        traits::MerkleParameters,
    };

    use snarkvm_circuits_environment::{assert_scope, Circuit, Mode};
    use snarkvm_curves::{bls12_377::Fr, edwards_bls12::EdwardsProjective};
    use snarkvm_utilities::{test_rng, ToBits, UniformRand};

    use std::sync::Arc;

    const PEDERSEN_NUM_WINDOWS: usize = 1;
    const PEDERSEN_LEAF_WINDOW_SIZE: usize = 251;
    const PEDERSEN_TWO_TO_ONE_WINDOW_SIZE: usize = 4;
    const TREE_DEPTH: usize = 4;
    const MESSAGE: &str = "Pedersen merkle path test";

    type NativeLeafCRH = NativePedersenCompressed<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
    type NativeTwoToOneCRH =
        NativePedersenCompressed<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_TWO_TO_ONE_WINDOW_SIZE>;
    type Parameters = MaskedMerkleTreeParameters<NativeLeafCRH, NativeTwoToOneCRH, TREE_DEPTH>;

    type LeafCRH = Pedersen<Circuit, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
    type TwoToOneCRH = Pedersen<Circuit, PEDERSEN_NUM_WINDOWS, PEDERSEN_TWO_TO_ONE_WINDOW_SIZE>;

    fn check_to_root(
        mode: Mode,
        use_bad_root: bool,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let merkle_tree_parameters = Parameters::setup(MESSAGE);
        let leaf_crh = LeafCRH::setup(MESSAGE);
        let two_to_one_crh = TwoToOneCRH::setup(MESSAGE);

        let mut rng = test_rng();
        let mut leaves = Vec::new();
        for _ in 0..1 << Parameters::DEPTH {
            leaves.push(Fr::rand(&mut rng));
        }

        let merkle_tree = MerkleTree::new(Arc::new(merkle_tree_parameters), &leaves).unwrap();
        let root = merkle_tree.root();

        for (i, leaf) in leaves.iter().enumerate() {
            let proof = merkle_tree.generate_proof(i, &leaf).unwrap();
            assert!(proof.verify(root, &leaf).unwrap());

            let leaf_bits = leaf.to_bits_le();
            let root = if use_bad_root { Default::default() } else { *root };

            let traversal = proof.position_list().collect::<Vec<_>>();
            let path = proof.path.clone();
            let merkle_path = MerklePath::<Circuit, TwoToOneCRH>::new(mode, (traversal, path));

            let circuit_leaf: Vec<Boolean<_>> = Inject::new(mode, leaf_bits);
            assert_eq!(*leaf.to_bits_le(), circuit_leaf.eject_value());

            Circuit::scope(format!("{mode} {MESSAGE} {i}"), || {
                let candidate_root = merkle_path.to_root(&leaf_crh, &two_to_one_crh, &circuit_leaf);
                assert_eq!(root, candidate_root.eject_value());

                let case = format!("mode = {mode}");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    // TODO (raychu86): Handle this test case.
    // Ignore this test for now. Pedersen Hashes have inconsistent constraint sizes when mode is Constant.
    #[ignore]
    #[test]
    fn test_to_root_constant() {
        check_to_root(Mode::Constant, false, 6742, 0, 0, 0);
    }

    #[ignore]
    #[test]
    fn test_to_root_public() {
        check_to_root(Mode::Public, false, 4545, 0, 15664, 15672);
    }

    #[ignore]
    #[test]
    fn test_to_root_private() {
        check_to_root(Mode::Private, false, 4545, 0, 15664, 15672);
    }

    #[should_panic]
    #[test]
    fn test_to_root_public_fails() {
        check_to_root(Mode::Public, true, 4545, 0, 15664, 15672);
    }

    #[should_panic]
    #[test]
    fn test_to_root_private_fails() {
        check_to_root(Mode::Private, true, 4545, 0, 15664, 15672);
    }
}
