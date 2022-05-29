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

mod helpers;
use helpers::{LeafHash, PathHash};

// mod to_root;

#[cfg(all(test, console))]
use snarkvm_circuit_types::environment::assert_scope;

use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field, U64};

use core::marker::PhantomData;

pub struct MerklePath<A: Aleo, LH: LeafHash<A>, PH: PathHash<A>, const DEPTH: u8> {
    /// The leaf index for the path.
    leaf_index: U64<A>,
    /// The `siblings` contains a list of sibling hashes from the leaf to the root.
    siblings: Vec<Field<A>>,
    /// PhantomData.
    _phantom: PhantomData<(LH, PH)>,
}

#[cfg(console)]
impl<A: Aleo, LH: LeafHash<A>, PH: PathHash<A>, const DEPTH: u8> Inject for MerklePath<A, LH, PH, DEPTH> {
    type Primitive = console::merkle_tree::MerklePath<A::Network, DEPTH>;

    /// Initializes a Merkle path from the given mode and native Merkle path.
    fn new(mode: Mode, merkle_path: Self::Primitive) -> Self {
        // Initialize the leaf index.
        let leaf_index = U64::new(mode, merkle_path.leaf_index());
        // Initialize the Merkle path siblings.
        let siblings: Vec<_> = merkle_path.siblings().iter().map(|node| Field::new(mode, *node)).collect();
        // Ensure the Merkle path is the correct depth.
        match siblings.len() == DEPTH as usize {
            // Return the Merkle path.
            true => Self { leaf_index, siblings, _phantom: PhantomData },
            false => A::halt("Merkle path is not the correct depth"),
        }
    }
}

#[cfg(console)]
impl<A: Aleo, LH: LeafHash<A>, PH: PathHash<A>, const DEPTH: u8> Eject for MerklePath<A, LH, PH, DEPTH> {
    type Primitive = console::merkle_tree::MerklePath<A::Network, DEPTH>;

    /// Ejects the mode of the Merkle path.
    fn eject_mode(&self) -> Mode {
        (&self.leaf_index, &self.siblings).eject_mode()
    }

    /// Ejects the Merkle path.
    fn eject_value(&self) -> Self::Primitive {
        match Self::Primitive::try_from((&self.leaf_index, &self.siblings).eject_value()) {
            Ok(merkle_path) => merkle_path,
            Err(error) => A::halt(format!("Failed to eject the Merkle path: {error}")),
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::Pedersen;
//
//     use snarkvm_algorithms::{
//         crh::PedersenCompressedCRH as NativePedersenCompressed,
//         merkle_tree::{MaskedMerkleTreeParameters, MerkleTree},
//         traits::MerkleParameters,
//     };
//     use snarkvm_circuit_types::environment::{assert_scope, Circuit, Mode};
//     use snarkvm_curves::{bls12_377::Fr, edwards_bls12::EdwardsProjective};
//     use snarkvm_utilities::{test_rng, UniformRand};
//
//     use std::sync::Arc;
//
//     const PEDERSEN_NUM_WINDOWS: usize = 128;
//     const PEDERSEN_LEAF_WINDOW_SIZE: usize = 2;
//     const PEDERSEN_TWO_TO_ONE_WINDOW_SIZE: usize = 4;
//     const TREE_DEPTH: usize = 4;
//     const MESSAGE: &str = "Pedersen merkle path test";
//
//     type NativeLeafCRH = NativePedersenCompressed<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_LEAF_WINDOW_SIZE>;
//     type NativeTwoToOneCRH =
//         NativePedersenCompressed<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_TWO_TO_ONE_WINDOW_SIZE>;
//     type Parameters = MaskedMerkleTreeParameters<NativeLeafCRH, NativeTwoToOneCRH, TREE_DEPTH>;
//
//     type TwoToOneCRH = Pedersen<Circuit, PEDERSEN_TWO_TO_ONE_WINDOW_SIZE>;
//
//     fn check_new(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
//         let merkle_tree_parameters = Parameters::setup(MESSAGE);
//
//         let mut rng = test_rng();
//         let mut leaves = Vec::new();
//         for _ in 0..1 << Parameters::DEPTH {
//             leaves.push(Fr::rand(&mut rng));
//         }
//
//         let merkle_tree = MerkleTree::new(Arc::new(merkle_tree_parameters), &leaves).unwrap();
//
//         for (i, leaf) in leaves.iter().enumerate() {
//             let proof = merkle_tree.generate_proof(i, &leaf).unwrap();
//
//             Circuit::scope(format!("{mode} {MESSAGE} {i}"), || {
//                 let traversal = proof.position_list().collect::<Vec<_>>();
//                 let path = proof.path.clone();
//                 let merkle_path = MerklePath::<Circuit, TwoToOneCRH>::new(mode, (traversal.clone(), path.clone()));
//
//                 assert_eq!((traversal, path), merkle_path.eject_value());
//                 assert_eq!(mode, merkle_path.eject_mode());
//
//                 let case = format!("mode = {mode}");
//                 assert_scope!(case, num_constants, num_public, num_private, num_constraints);
//             });
//         }
//     }
//
//     #[test]
//     fn test_merkle_path_new() {
//         check_new(Mode::Constant, 8, 0, 0, 0);
//         check_new(Mode::Private, 0, 0, 8, 4);
//         check_new(Mode::Public, 0, 8, 0, 4);
//     }
// }
