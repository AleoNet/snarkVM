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

// #[cfg(all(test, console))]
// pub(crate) mod tests {
//     use super::*;
//     use crate::{helpers::generate_account};
//     use snarkvm_circuit_network::AleoV0 as Circuit;
//
//     use anyhow::Result;
//
//     const ITERATIONS: u64 = 100;
//
//     fn check_new(
//         mode: Mode,
//         num_constants: u64,
//         num_public: u64,
//         num_private: u64,
//         num_constraints: u64,
//     ) -> Result<()> {
//
//         // Construct the Merkle tree for the given leaves.
//         type LH =
//         let merkle_tree = console::merkle_tree::MerkleTree::<N, LH, PH, DEPTH>::new(leaf_hasher, path_hasher, leaves)?;
//         assert_eq!(leaves.len(), merkle_tree.number_of_leaves);
//
//         // Check each leaf in the Merkle tree.
//         if !leaves.is_empty() {
//             for (leaf_index, leaf) in leaves.iter().enumerate() {
//                 // Compute a Merkle proof for the leaf.
//                 let proof = merkle_tree.prove(leaf_index, leaf)?;
//                 // Verify the Merkle proof succeeds.
//                 assert!(proof.verify(leaf_hasher, path_hasher, merkle_tree.root(), leaf));
//                 // Verify the Merkle proof **fails** on an invalid root.
//                 assert!(!proof.verify(leaf_hasher, path_hasher, &N::Field::zero(), leaf));
//                 assert!(!proof.verify(leaf_hasher, path_hasher, &N::Field::one(), leaf));
//                 assert!(!proof.verify(leaf_hasher, path_hasher, &N::Field::rand(&mut test_rng()), leaf));
//             }
//         }
//         // If additional leaves are provided, check that the Merkle tree is consistent with them.
//         if !additional_leaves.is_empty() {
//             // Append additional leaves to the Merkle tree.
//             let merkle_tree = merkle_tree.append(additional_leaves)?;
//             // Check each additional leaf in the Merkle tree.
//             for (leaf_index, leaf) in additional_leaves.iter().enumerate() {
//                 // Compute a Merkle proof for the leaf.
//                 let proof = merkle_tree.prove(leaves.len() + leaf_index, leaf)?;
//                 // Verify the Merkle proof succeeds.
//                 assert!(proof.verify(leaf_hasher, path_hasher, merkle_tree.root(), leaf));
//                 // Verify the Merkle proof **fails** on an invalid root.
//                 assert!(!proof.verify(leaf_hasher, path_hasher, &N::Field::zero(), leaf));
//                 assert!(!proof.verify(leaf_hasher, path_hasher, &N::Field::one(), leaf));
//                 assert!(!proof.verify(leaf_hasher, path_hasher, &N::Field::rand(&mut test_rng()), leaf));
//             }
//         }
//         Ok(())
//
//
//         for i in 0..ITERATIONS {
//
//             Circuit::scope(format!("New {mode}"), || {
//                 let candidate = ComputeKey::<Circuit>::new(mode, compute_key);
//                 match mode.is_constant() {
//                     true => assert_eq!(Mode::Constant, candidate.eject_mode()),
//                     false => assert_eq!(Mode::Private, candidate.eject_mode()),
//                 };
//                 assert_eq!(compute_key, candidate.eject_value());
//                 // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
//                 if i > 0 {
//                     assert_scope!(num_constants, num_public, num_private, num_constraints);
//                 }
//             });
//             Circuit::reset();
//         }
//         Ok(())
//     }
//
//     #[test]
//     fn test_new_constant() -> Result<()> {
//         check_new(Mode::Constant, 266, 0, 0, 0)
//     }
//
//     #[test]
//     fn test_new_public() -> Result<()> {
//         check_new(Mode::Public, 7, 6, 604, 608)
//     }
//
//     #[test]
//     fn test_new_private() -> Result<()> {
//         check_new(Mode::Private, 7, 0, 610, 608)
//     }
// }
