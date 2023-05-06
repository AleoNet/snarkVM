// Copyright (C) 2019-2023 Aleo Systems Inc.
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

pub mod benchmark;
pub use benchmark::*;

pub mod object_store;
pub use object_store::*;

pub mod workload;
pub use workload::*;

use console::{
    account::{PrivateKey, ViewKey},
    network::Testnet3,
    prelude::Network,
    program::{Field, Literal, Plaintext, Record, Value, Zero, U64},
};
use snarkvm_synthesizer::{
    Block,
    ConsensusStorage,
    ConsensusStore,
    Header,
    Metadata,
    Transaction,
    Transactions,
    Transition,
    VM,
};
use snarkvm_utilities::TestRng;

use anyhow::Result;
use indexmap::IndexMap;
use rand::{CryptoRng, Rng};
use std::borrow::Borrow;

/// A helper function to initialize a VM with a genesis block.
pub fn initialize_vm<C: ConsensusStorage<Testnet3>, R: Rng + CryptoRng>(
    private_key: &PrivateKey<Testnet3>,
    rng: &mut R,
) -> (VM<Testnet3, C>, Record<Testnet3, Plaintext<Testnet3>>) {
    // Initialize the VM.
    #[cfg(any(feature = "testing"))]
    let vm = {
        // If the `rocks` feature is enabled, then we are benchmarking using the DB backend.
        // This block creates a temporary directory for the database.
        let temp_dir = match cfg!(feature = "rocks") {
            false => None,
            true => {
                let temp_dir = tempfile::tempdir().expect("Failed to open temporary directory").into_path();
                println!("Using the following temporary directory {:?}", temp_dir);
                Some(temp_dir)
            }
        };
        VM::from(ConsensusStore::open_testing(temp_dir).unwrap()).unwrap()
    };
    #[cfg(not(any(feature = "testing")))]
    let vm = VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Initialize the genesis block.
    let genesis = Block::genesis(&vm, private_key, rng).unwrap();

    // Fetch the unspent records.
    let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

    // Select a record to spend.
    let view_key = ViewKey::try_from(private_key).unwrap();
    let record = records.values().next().unwrap().decrypt(&view_key).unwrap();

    // Update the VM.
    vm.add_next_block(&genesis).unwrap();

    (vm, record)
}

#[allow(unused)]
/// Construct a new block based on the given transactions.
pub fn construct_next_block<C: ConsensusStorage<Testnet3>, R: Rng + CryptoRng>(
    vm: &VM<Testnet3, C>,
    private_key: &PrivateKey<Testnet3>,
    transactions: &[Transaction<Testnet3>],
    rng: &mut R,
) -> Result<Block<Testnet3>> {
    // Get the most recent block.
    let block_hash =
        vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
    let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();

    // Construct the new block header.
    let transactions = Transactions::from(transactions);
    // Construct the metadata associated with the block.
    let metadata = Metadata::new(
        Testnet3::ID,
        previous_block.round() + 1,
        previous_block.height() + 1,
        Testnet3::STARTING_SUPPLY,
        0,
        Testnet3::GENESIS_COINBASE_TARGET,
        Testnet3::GENESIS_PROOF_TARGET,
        previous_block.last_coinbase_target(),
        previous_block.last_coinbase_timestamp(),
        Testnet3::GENESIS_TIMESTAMP + 1,
    )?;

    let header = Header::from(
        *vm.block_store().current_state_root(),
        transactions.to_root().unwrap(),
        Field::zero(),
        Field::zero(),
        metadata,
    )?;

    // Construct the new block.
    Block::new(private_key, previous_block.hash(), header, transactions, None, rng)
}

#[allow(unused)]
type SplitOutput =
    (Record<Testnet3, Plaintext<Testnet3>>, Record<Testnet3, Plaintext<Testnet3>>, Transaction<Testnet3>);
#[allow(unused)]
/// A helper function to invoke the `split` function an a credits.aleo record.
pub fn split<C: ConsensusStorage<Testnet3>>(
    vm: &VM<Testnet3, C>,
    private_key: &PrivateKey<Testnet3>,
    record: Record<Testnet3, Plaintext<Testnet3>>,
    amount: u64,
    rng: &mut TestRng,
) -> SplitOutput {
    let authorization = vm
        .authorize(
            private_key,
            "credits.aleo",
            "split",
            vec![Value::Record(record), Value::Plaintext(Plaintext::from(Literal::U64(U64::new(amount))))],
            rng,
        )
        .unwrap();
    let (response, execution, _) = vm.execute(authorization, None, rng).unwrap();

    let transaction = Transaction::from_execution(execution, None).unwrap();

    match (response.outputs()[0].clone(), response.outputs()[1].clone()) {
        (Value::Record(fee_record), Value::Record(remaining_record)) => (fee_record, remaining_record, transaction),
        _ => unreachable!("`split` always returns a record"),
    }
}
