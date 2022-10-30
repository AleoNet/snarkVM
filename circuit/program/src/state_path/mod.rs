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

mod header_leaf;
pub use header_leaf::*;

mod transaction_leaf;
pub use transaction_leaf::*;

mod transition_leaf;
pub use transition_leaf::*;

use snarkvm_circuit_collections::merkle_tree::MerklePath;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field};

/// The depth of the Merkle tree for the blocks.
const BLOCKS_DEPTH: u8 = console::BLOCKS_DEPTH;
/// The depth of the Merkle tree for the block header.
const HEADER_DEPTH: u8 = console::HEADER_DEPTH;
/// The depth of the Merkle tree for transactions in a block.
const TRANSACTIONS_DEPTH: u8 = console::TRANSACTIONS_DEPTH;
/// The depth of the Merkle tree for the transaction.
const TRANSACTION_DEPTH: u8 = console::TRANSACTION_DEPTH;
/// The depth of the Merkle tree for the transition.
const TRANSITION_DEPTH: u8 = console::TRANSITION_DEPTH;

type BlockPath<A> = MerklePath<A, BLOCKS_DEPTH>;
type HeaderPath<A> = MerklePath<A, HEADER_DEPTH>;
type TransactionsPath<A> = MerklePath<A, TRANSACTIONS_DEPTH>;
type TransactionPath<A> = MerklePath<A, TRANSACTION_DEPTH>;
type TransitionPath<A> = MerklePath<A, TRANSITION_DEPTH>;

pub struct StatePath<A: Aleo> {
    /// The state root.
    state_root: Field<A>,
    /// The Merkle path for the block hash.
    block_path: BlockPath<A>,
    /// The block hash.
    block_hash: Field<A>,
    /// The previous block hash.
    previous_block_hash: Field<A>,
    /// The block header root.
    header_root: Field<A>,
    /// The Merkle path for the block header leaf.
    header_path: HeaderPath<A>,
    /// The block header leaf.
    header_leaf: HeaderLeaf<A>,
    /// The Merkle path for the transaction ID.
    transactions_path: TransactionsPath<A>,
    /// The transaction ID.
    transaction_id: Field<A>,
    /// The Merkle path for the transaction leaf.
    transaction_path: TransactionPath<A>,
    /// The transaction leaf.
    transaction_leaf: TransactionLeaf<A>,
    /// The Merkle path for the transition leaf.
    transition_path: TransitionPath<A>,
    /// The transition leaf.
    transition_leaf: TransitionLeaf<A>,
}

impl<A: Aleo> StatePath<A> {
    /// Returns the transition leaf.
    pub const fn transition_leaf(&self) -> &TransitionLeaf<A> {
        &self.transition_leaf
    }
}

impl<A: Aleo> Inject for StatePath<A> {
    type Primitive = console::StatePath<A::Network>;

    /// Initializes a new ciphertext circuit from a primitive.
    fn new(mode: Mode, state_path: Self::Primitive) -> Self {
        Self {
            state_root: Field::new(Mode::Public, *state_path.state_root()),
            block_path: BlockPath::new(mode, state_path.block_path().clone()),
            block_hash: Field::new(mode, *state_path.block_hash()),
            previous_block_hash: Field::new(mode, *state_path.previous_block_hash()),
            header_root: Field::new(mode, *state_path.header_root()),
            header_path: HeaderPath::new(mode, state_path.header_path().clone()),
            header_leaf: HeaderLeaf::new(mode, state_path.header_leaf().clone()),
            transactions_path: TransactionsPath::new(mode, state_path.transactions_path().clone()),
            transaction_id: Field::new(mode, **state_path.transaction_id()),
            transaction_path: TransactionPath::new(mode, state_path.transaction_path().clone()),
            transaction_leaf: TransactionLeaf::new(mode, state_path.transaction_leaf().clone()),
            transition_path: TransitionPath::new(mode, state_path.transition_path().clone()),
            transition_leaf: TransitionLeaf::new(mode, state_path.transition_leaf().clone()),
        }
    }
}

impl<A: Aleo> Eject for StatePath<A> {
    type Primitive = console::StatePath<A::Network>;

    /// Ejects the mode of the state path.
    fn eject_mode(&self) -> Mode {
        Mode::combine(self.state_root.eject_mode(), [
            self.block_path.eject_mode(),
            self.block_hash.eject_mode(),
            self.previous_block_hash.eject_mode(),
            self.header_root.eject_mode(),
            self.header_path.eject_mode(),
            self.header_leaf.eject_mode(),
            self.transactions_path.eject_mode(),
            self.transaction_id.eject_mode(),
            self.transaction_path.eject_mode(),
            self.transaction_leaf.eject_mode(),
            self.transition_path.eject_mode(),
            self.transition_leaf.eject_mode(),
        ])
    }

    /// Ejects the state path.
    fn eject_value(&self) -> Self::Primitive {
        match Self::Primitive::from(
            self.state_root.eject_value().into(),
            self.block_path.eject_value(),
            self.block_hash.eject_value().into(),
            self.previous_block_hash.eject_value().into(),
            self.header_root.eject_value(),
            self.header_path.eject_value(),
            self.header_leaf.eject_value(),
            self.transactions_path.eject_value(),
            self.transaction_id.eject_value().into(),
            self.transaction_path.eject_value(),
            self.transaction_leaf.eject_value(),
            self.transition_path.eject_value(),
            self.transition_leaf.eject_value(),
        ) {
            Ok(state_path) => state_path,
            Err(error) => A::halt(format!("Failed to eject the state path: {error}")),
        }
    }
}

impl<A: Aleo> StatePath<A> {
    /// Returns `true` if the state path is valid.
    pub fn verify(&self) -> Boolean<A> {
        // Ensure the transition path is valid.
        let check_transition_path = A::verify_merkle_path_bhp(
            &self.transition_path,
            self.transaction_leaf.id(),
            &self.transition_leaf.to_bits_le(),
        );

        // Ensure the transaction path is valid.
        let check_transaction_path = A::verify_merkle_path_bhp(
            &self.transaction_path,
            &self.transaction_id,
            &self.transaction_leaf.to_bits_le(),
        );

        // Ensure the transactions path is valid.
        let check_transactions_path = A::verify_merkle_path_bhp(
            &self.transactions_path,
            self.header_leaf.id(),
            &self.transaction_id.to_bits_le(),
        );

        // Ensure the header path is valid.
        let check_header_path =
            A::verify_merkle_path_bhp(&self.header_path, &self.header_root, &self.header_leaf.to_bits_le());

        // Construct the block hash preimage.
        let block_hash_preimage = self
            .previous_block_hash
            .to_bits_le()
            .into_iter()
            .chain(self.header_root.to_bits_le().into_iter())
            .collect::<Vec<_>>();

        // Ensure the block path is valid.
        let check_block_hash = A::hash_bhp1024(&block_hash_preimage).is_equal(&self.block_hash);

        // Ensure the state root is correct.
        let check_state_root =
            A::verify_merkle_path_bhp(&self.block_path, &self.state_root, &self.block_hash.to_bits_le());

        check_transition_path
            & check_transaction_path
            & check_transactions_path
            & check_header_path
            & check_block_hash
            & check_state_root
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::snark::UniversalSRS;
//     use circuit::{
//         environment::{Circuit, Inject},
//         network::AleoV0,
//         Mode,
//     };
//     use console::{network::Testnet3, program::Identifier};
//     use snarkvm_utilities::rand::TestRng;
//
//     type CurrentAleo = AleoV0;
//     type CurrentNetwork = Testnet3;
//
//     #[test]
//     fn test_verify() {
//         let rng = &mut TestRng::default();
//
//         // Initialize the ledger.
//         let ledger = crate::state_path::test_helpers::TestLedger::new(rng).unwrap();
//         // Retrieve the genesis block.
//         let genesis = ledger.get_block(0).unwrap();
//
//         for mode in [Mode::Constant, Mode::Public, Mode::Private].into_iter() {
//             for commitment in genesis.commitments() {
//                 // Construct the console state path.
//                 let console_state_path = ledger.to_state_path(commitment).unwrap();
//                 // Construct the circuit state path.
//                 let circuit_state_path = StatePath::<CurrentAleo>::new(mode, console_state_path);
//
//                 // Ensure the state path is valid.
//                 let is_valid = circuit_state_path.verify();
//                 assert!(is_valid.eject_value());
//                 assert!(CurrentAleo::is_satisfied());
//                 CurrentAleo::reset();
//             }
//         }
//     }
//
//     fn check_batch_verify(mode: Mode, batch_size: usize) {
//         let rng = &mut TestRng::default();
//
//         // Initialize the ledger.
//         let ledger = crate::state_path::test_helpers::TestLedger::new(rng).unwrap();
//         // Retrieve the genesis block.
//         let genesis = ledger.get_block(0).unwrap();
//
//         // Construct the assignments.
//         let mut assignments = Vec::with_capacity(batch_size);
//
//         // Construct the verification inputs.
//         let mut inputs = vec![];
//
//         for _ in 0..batch_size {
//             let commitment = genesis.commitments().next().unwrap();
//             // Construct the console state path.
//             let console_state_path = ledger.to_state_path(commitment).unwrap();
//             // Construct the circuit state path.
//             let circuit_state_path = StatePath::<CurrentAleo>::new(mode, console_state_path.clone());
//
//             // Ensure the state path is valid.
//             let is_valid = circuit_state_path.verify();
//             assert!(is_valid.eject_value());
//             assert!(CurrentAleo::is_satisfied());
//
//             let assignment = CurrentAleo::eject_assignment_and_reset();
//             Circuit::reset();
//
//             inputs.push(vec![<Circuit as Environment>::BaseField::one(), **console_state_path.state_root]);
//
//             assignments.push(assignment);
//         }
//
//         // Construct the proving and verifying keys.
//         let universal_srs = UniversalSRS::<CurrentNetwork>::load().unwrap();
//         let function_name = Identifier::<CurrentNetwork>::from_str(&format!("state_paths_{batch_size}")).unwrap();
//         let (proving_key, verifying_key) = universal_srs.to_circuit_key(&function_name, &assignments[0]).unwrap();
//
//         // Generate the batch proof.
//         let batch_proof = proving_key.prove_batch(&function_name, &assignments, rng).unwrap();
//
//         // Verify the batch proof.
//         let batch_verify = verifying_key.verify_batch(&function_name, inputs.as_slice(), &batch_proof);
//         assert!(batch_verify);
//     }
//
//     #[test]
//     fn test_state_path_batch_1() {
//         check_batch_verify(Mode::Private, 1);
//     }
//
//     #[test]
//     fn test_state_path_batch_2() {
//         check_batch_verify(Mode::Private, 2);
//     }
//
//     #[test]
//     fn test_state_path_batch_4() {
//         check_batch_verify(Mode::Private, 4);
//     }
//
//     #[test]
//     fn test_state_path_batch_8() {
//         check_batch_verify(Mode::Private, 8);
//     }
// }
