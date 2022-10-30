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

/// The circuit for state path verification.
pub fn inject_and_verify_state_path<N: console::network::Network, A: circuit::Aleo<Network = N>>(
    state_path: console::program::StatePath<N>,
    commitment: console::types::Field<N>,
) {
    use circuit::Inject;

    // Allocate the state path circuit.
    let state_path_circuit = circuit::StatePath::<A>::new(circuit::Mode::Private, state_path);
    // Allocate the commitment circuit.
    let commitment_circuit = circuit::Field::<A>::new(circuit::Mode::Private, commitment);

    A::assert_eq(state_path_circuit.transition_leaf().id(), commitment_circuit);

    A::assert(state_path_circuit.verify())
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
                ledger.vm.block_store().insert(*ledger.block_tree.root(), block)?;

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
            self.vm.block_store().get_state_path_for_commitment(&self.block_tree, commitment)
        }
    }
}
