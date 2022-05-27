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

// mod to_root;

use crate::Hash;
use snarkvm_circuit_types::{environment::prelude::*, Boolean};

pub struct MerklePath<E: Environment, TwoToOneCRH: Hash> {
    /// `traversal[i]` is 0 (false) iff ith node from bottom to top is left.
    traversal: Vec<Boolean<E>>,
    /// `path[i]` is the entry of sibling of ith node from bottom to top.
    path: Vec<TwoToOneCRH::Output>,
}

impl<E: Environment, TwoToOneCRH: Hash> Inject for MerklePath<E, TwoToOneCRH> {
    type Primitive = (Vec<bool>, Vec<<TwoToOneCRH::Output as Inject>::Primitive>);

    /// Initializes a merkle path from the given mode and `path`.
    fn new(mode: Mode, (traversal, path): Self::Primitive) -> Self {
        let mut circuit_traversal = vec![];
        for position in traversal.iter() {
            circuit_traversal.push(Boolean::new(mode, *position));
        }

        let mut circuit_path = vec![];
        for node in path.into_iter() {
            circuit_path.push(TwoToOneCRH::Output::new(mode, node));
        }

        Self { traversal: circuit_traversal, path: circuit_path }
    }
}

impl<E: Environment, TwoToOneCRH: Hash> Eject for MerklePath<E, TwoToOneCRH> {
    type Primitive = (Vec<bool>, Vec<<TwoToOneCRH::Output as Eject>::Primitive>);

    ///
    /// Ejects the mode of the merkle path.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.traversal, &self.path).eject_mode()
    }

    ///
    /// Ejects the merkle path as `(traversal, path)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.traversal, &self.path).eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Pedersen;

    use snarkvm_algorithms::{
        crh::PedersenCompressedCRH as NativePedersenCompressed,
        merkle_tree::{MaskedMerkleTreeParameters, MerkleTree},
        traits::MerkleParameters,
    };
    use snarkvm_circuit_environment::{assert_scope, Circuit, Mode};
    use snarkvm_curves::{bls12_377::Fr, edwards_bls12::EdwardsProjective};
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::sync::Arc;

    const PEDERSEN_NUM_WINDOWS: usize = 128;
    const PEDERSEN_LEAF_WINDOW_SIZE: usize = 2;
    const PEDERSEN_TWO_TO_ONE_WINDOW_SIZE: usize = 4;
    const TREE_DEPTH: usize = 4;
    const MESSAGE: &str = "Pedersen merkle path test";

    type NativeLeafCRH = NativePedersenCompressed<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
    type NativeTwoToOneCRH =
        NativePedersenCompressed<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_TWO_TO_ONE_WINDOW_SIZE>;
    type Parameters = MaskedMerkleTreeParameters<NativeLeafCRH, NativeTwoToOneCRH, TREE_DEPTH>;

    type TwoToOneCRH = Pedersen<Circuit, PEDERSEN_NUM_WINDOWS, PEDERSEN_TWO_TO_ONE_WINDOW_SIZE>;

    fn check_new(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        let merkle_tree_parameters = Parameters::setup(MESSAGE);

        let mut rng = test_rng();
        let mut leaves = Vec::new();
        for _ in 0..1 << Parameters::DEPTH {
            leaves.push(Fr::rand(&mut rng));
        }

        let merkle_tree = MerkleTree::new(Arc::new(merkle_tree_parameters), &leaves).unwrap();

        for (i, leaf) in leaves.iter().enumerate() {
            let proof = merkle_tree.generate_proof(i, &leaf).unwrap();

            Circuit::scope(format!("{mode} {MESSAGE} {i}"), || {
                let traversal = proof.position_list().collect::<Vec<_>>();
                let path = proof.path.clone();
                let merkle_path = MerklePath::<Circuit, TwoToOneCRH>::new(mode, (traversal.clone(), path.clone()));

                assert_eq!((traversal, path), merkle_path.eject_value());
                assert_eq!(mode, merkle_path.eject_mode());

                let case = format!("mode = {mode}");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_merkle_path_new() {
        check_new(Mode::Constant, 8, 0, 0, 0);
        check_new(Mode::Private, 0, 0, 8, 4);
        check_new(Mode::Public, 0, 8, 0, 4);
    }
}
