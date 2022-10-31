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

#![forbid(unsafe_code)]
#![allow(clippy::module_inception)]
#![allow(clippy::single_element_loop)]
// TODO (howardwu): Remove me after tracing.
#![allow(clippy::print_in_format_impl)]
#![cfg_attr(test, allow(clippy::assertions_on_result_states))]

#[macro_use]
extern crate tracing;

pub mod block;
pub use block::*;

pub mod coinbase_puzzle;
pub use coinbase_puzzle::*;

pub mod process;
pub use process::*;

pub mod program;
pub use program::*;

pub mod snark;
pub use snark::*;

pub mod store;
pub use store::*;

pub mod vm;
pub use vm::*;

use console::{
    network::Network,
    prelude::Zero,
    program::StatePath,
    types::{Field, Group},
};

use anyhow::{ensure, Result};

/// The circuit for state path verification.
///
/// # Diagram
/// The `[[ ]]` notation is used to denote public inputs.
/// ```ignore
///             [[ global_state_root ]] || [[ local_state_root ]]
///                        |                          |
///                        -------- is_global --------
///                                     |
///                                state_path
///                                    |
/// [[ serial_number ]] := Commit( commitment || Hash( COFACTOR * gamma ) )
/// ```
pub fn inject_and_verify_state_path<N: Network, A: circuit::Aleo<Network = N>>(
    console_state_path: StatePath<N>,
    console_commitment: Field<N>,
    console_gamma: Group<N>,
    console_serial_number: Field<N>,
    console_local_state_root: Field<N>,
    console_is_global: bool,
) -> Result<circuit::Assignment<N::Field>> {
    use circuit::Inject;

    // As the local state root feature is currently unused, we check that `local_state_root` is zero,
    // and that `is_global` is true.
    ensure!(console_local_state_root.is_zero());
    ensure!(console_is_global);

    // Ensure the circuit environment is clean.
    assert_eq!(A::count(), (0, 1, 0, 0, 0));
    A::reset();

    // Inject the state path as `Mode::Private` (with a global state root as `Mode::Public`).
    let state_path = circuit::StatePath::<A>::new(circuit::Mode::Private, console_state_path);
    // Inject the commitment as `Mode::Private`.
    let commitment = circuit::Field::<A>::new(circuit::Mode::Private, console_commitment);
    // Inject the gamma as `Mode::Private`.
    let gamma = circuit::Group::<A>::new(circuit::Mode::Private, console_gamma);

    // Inject the local state root as `Mode::Public`.
    let local_state_root = circuit::Field::<A>::new(circuit::Mode::Public, console_local_state_root);
    // Inject the 'is_global' flag as `Mode::Private`.
    let is_global = circuit::Boolean::<A>::new(circuit::Mode::Private, console_is_global);

    // Inject the serial number as `Mode::Public`.
    let serial_number = circuit::Field::<A>::new(circuit::Mode::Public, console_serial_number);
    // Compute the candidate serial number.
    let candidate_serial_number =
        circuit::Record::<A, circuit::Plaintext<A>>::serial_number_from_gamma(&gamma, commitment.clone());
    // Enforce that the candidate serial number is equal to the serial number.
    A::assert_eq(&candidate_serial_number, &serial_number);

    // Enforce the starting leaf is the claimed commitment.
    A::assert_eq(state_path.transition_leaf().id(), commitment);
    // Enforce the state path from leaf to root is correct.
    A::assert(state_path.verify(&is_global, &local_state_root));

    #[cfg(debug_assertions)]
    Stack::log_circuit::<A, _>(&format!("State Path for {console_serial_number}"));

    // Eject the assignment and reset the circuit environment.
    Ok(A::eject_assignment_and_reset())
}

#[cfg(test)]
#[allow(dead_code)]
pub(crate) mod test_helpers {
    use crate::{
        block::Block,
        store::{ConsensusMemory, ConsensusStore},
        vm::VM,
    };
    use console::{
        network::Testnet3,
        prelude::{Network, TestRng, ToBits},
        program::{BlockTree, StatePath},
        types::Field,
    };

    use anyhow::{bail, Result};

    type CurrentNetwork = Testnet3;

    #[derive(Clone)]
    pub struct TestLedger<N: Network> {
        /// The VM state.
        vm: VM<N, ConsensusMemory<N>>,
        /// The current block tree.
        block_tree: BlockTree<N>,
    }

    impl TestLedger<CurrentNetwork> {
        /// Initializes a new instance of the ledger.
        pub fn new(rng: &mut TestRng) -> Result<Self> {
            // Initialize the genesis block.
            let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

            // Initialize the consensus store.
            let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
            // Initialize a new VM.
            let vm = VM::from(store)?;

            // Initialize the ledger.
            let mut ledger = Self { vm, block_tree: CurrentNetwork::merkle_tree_bhp(&[])? };

            // Add the genesis block.
            ledger.add_next_block(&genesis)?;

            // Return the ledger.
            Ok(ledger)
        }
    }

    impl<N: Network> TestLedger<N> {
        /// Adds the given block as the next block in the chain.
        pub fn add_next_block(&mut self, block: &Block<N>) -> Result<()> {
            /* ATOMIC CODE SECTION */

            // Add the block to the ledger. This code section executes atomically.
            {
                let mut ledger = self.clone();

                // Update the blocks.
                ledger.block_tree.append(&[block.hash().to_bits_le()])?;
                let block_path = ledger.block_tree.prove(block.height() as usize, &block.hash().to_bits_le())?;
                ledger.vm.block_store().insert(*ledger.block_tree.root(), block_path, block)?;

                // Update the VM.
                for transaction in block.transactions().values() {
                    ledger.vm.finalize(transaction)?;
                }

                *self = Self { vm: ledger.vm, block_tree: ledger.block_tree };
            }

            Ok(())
        }

        /// Returns the block for the given block height.
        pub fn get_block(&self, height: u32) -> Result<Block<N>> {
            // Retrieve the block hash.
            let block_hash = match self.vm.block_store().get_block_hash(height)? {
                Some(block_hash) => block_hash,
                None => bail!("Block {height} does not exist in storage"),
            };
            // Retrieve the block.
            match self.vm.block_store().get_block(&block_hash)? {
                Some(block) => Ok(block),
                None => bail!("Block {height} ('{block_hash}') does not exist in storage"),
            }
        }

        /// Returns a state path for the given commitment.
        pub fn to_state_path(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
            self.vm.block_store().get_state_path_for_commitment(commitment, Some(&self.block_tree))
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::Circuit;
//     use snarkvm_utilities::rand::TestRng;
//
//     type CurrentAleo = Circuit;
//     type CurrentNetwork = <Circuit as Environment>::Network;
//
//     const ITERATIONS: usize = 100;
//
//     // use crate::snark::UniversalSRS;
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
//         let function_name = console::Identifier::<CurrentNetwork>::from_str(&format!("state_paths_{batch_size}")).unwrap();
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
