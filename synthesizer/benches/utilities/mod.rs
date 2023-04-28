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

pub mod workload;
pub use workload::*;

use console::{
    account::{PrivateKey, ViewKey},
    network::Testnet3,
    prelude::Network,
    program::{Field, Identifier, Literal, Plaintext, ProgramID, Record, Value, Zero, U64},
};
use snarkvm_synthesizer::{
    Block,
    Certificate,
    ConsensusMemory,
    ConsensusStore,
    Deployment,
    Fee,
    Header,
    Input,
    Metadata,
    Output,
    Program,
    Proof,
    Transaction,
    Transactions,
    Transition,
    VerifyingKey,
    VM,
};
use snarkvm_utilities::{TestRng, Uniform};

use anyhow::Result;
use indexmap::IndexMap;
use itertools::Itertools;
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::{borrow::Borrow, iter, str::FromStr};

/// A helper function to initialize a VM with a genesis block.
pub fn initialize_vm<R: Rng + CryptoRng>(
    private_key: &PrivateKey<Testnet3>,
    rng: &mut R,
) -> (VM<Testnet3, ConsensusMemory<Testnet3>>, Record<Testnet3, Plaintext<Testnet3>>) {
    let vm = VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Initialize the genesis block.
    let genesis = Block::genesis(&vm, private_key, rng).unwrap();

    // Fetch the unspent records.
    let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

    // Select a record to spend.
    let view_key = ViewKey::try_from(private_key).unwrap();
    let record = records.values().next().unwrap().decrypt(&view_key).unwrap();

    // Update the VM.
    vm.add_next_block(&genesis, None).unwrap();

    (vm, record)
}

#[allow(unused)]
/// Construct a new block based on the given transactions.
pub fn construct_next_block<R: Rng + CryptoRng>(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
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

    let header =
        Header::from(*vm.block_store().current_state_root(), transactions.to_root().unwrap(), Field::zero(), metadata)?;

    // Construct the new block.
    Block::new(private_key, previous_block.hash(), header, transactions, None, rng)
}

#[allow(unused)]
/// A helper function that deploys and executes programs.
pub fn setup(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    batches: &[Vec<Operation<Testnet3>>],
    rng: &mut TestRng,
) {
    // For each batch of setup operations, construct and add a block.
    for operations in batches {
        // Storage for the transactions.
        let mut transactions = Vec::with_capacity(operations.len());
        // Construct transactions for the operations.
        for operation in operations {
            match operation {
                Operation::Deploy(program) => {
                    // Construct a transaction for the deployment.
                    transactions.push(mock_deployment_transaction(private_key, *program.clone(), rng));
                }
                Operation::Execute(program_id, function_name, inputs) => {
                    let authorization = vm.authorize(private_key, program_id, function_name, inputs, rng).unwrap();
                    let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
                    transactions.push(Transaction::from_execution(execution, Some(mock_fee(rng))).unwrap());
                }
            }
        }
        // Create and add a block for the transactions, if any
        if !transactions.is_empty() {
            let block = construct_next_block(vm, private_key, &transactions, rng).unwrap();
            vm.add_next_block(&block, None).unwrap();
        }
    }
}

#[allow(unused)]
/// A helper function to invoke the `split` function an a credits.aleo record.
pub fn split(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    record: Record<Testnet3, Plaintext<Testnet3>>,
    amount: u64,
    rng: &mut TestRng,
) -> (Record<Testnet3, Plaintext<Testnet3>>, Record<Testnet3, Plaintext<Testnet3>>) {
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

    // Create and add a block for the fee transaction.
    let block =
        construct_next_block(vm, private_key, &[Transaction::from_execution(execution, None).unwrap()], rng).unwrap();
    vm.add_next_block(&block, None).unwrap();

    match (response.outputs()[0].clone(), response.outputs()[1].clone()) {
        (Value::Record(fee_record), Value::Record(remaining_record)) => (fee_record, remaining_record),
        _ => unreachable!("`split` always returns a record"),
    }
}

#[allow(unused)]
/// Samples a proof for a fee transition.
pub fn sample_proof() -> Proof<Testnet3> {
    static INSTANCE: OnceCell<Proof<Testnet3>> = OnceCell::new();
    INSTANCE
        .get_or_init(|| {
            let rng = &mut TestRng::default();
            let private_key = PrivateKey::new(rng).unwrap();
            let (vm, record) = initialize_vm(&private_key, rng);
            // Sample a fee.
            let (_, fee, _) = vm.execute_fee(&private_key, record, 1u64, None, rng).unwrap();
            // Return the proof.
            fee.transition().proof().clone()
        })
        .clone()
}

#[cfg(feature = "test-utilities")]
/// Constructs a deployment transaction without the overhead of synthesis.
pub fn mock_deployment_transaction(
    private_key: &PrivateKey<Testnet3>,
    program: Program<Testnet3>,
    rng: &mut TestRng,
) -> Transaction<Testnet3> {
    // Construct a mock fee for the deployment.
    let fee = mock_fee(rng);
    // Construct mock verifying keys.
    let verifying_keys = program
        .functions()
        .iter()
        .map(|(identifier, _)| (*identifier, (VerifyingKey::mock(), Certificate::mock(identifier).unwrap())))
        .collect_vec();
    // Construct an unchecked deployment.
    let deployment = Deployment::new_unchecked(Testnet3::EDITION, program, verifying_keys);
    // Construct a transaction for the deployment.
    Transaction::from_deployment_and_fee(private_key, deployment, fee, rng).unwrap()
}

#[allow(unused)]
/// Constructs a mock fee without the overhead of execution.
pub fn mock_fee(rng: &mut TestRng) -> Fee<Testnet3> {
    let proof = sample_proof();
    Fee::from(
        Transition::new(
            ProgramID::from_str("credits.aleo").unwrap(),
            Identifier::from_str("fee").unwrap(),
            iter::repeat_with(|| Input::Private(Field::rand(rng), None)).take(Testnet3::MAX_INPUTS).collect_vec(),
            iter::repeat_with(|| Output::Private(Field::rand(rng), None)).take(Testnet3::MAX_OUTPUTS).collect_vec(),
            None,
            proof,
            console::types::Group::zero(),
            Field::zero(),
        )
        .unwrap(),
        <Testnet3 as Network>::StateRoot::default(),
        None,
    )
}

#[cfg(feature = "test-utilities")]
#[allow(clippy::type_complexity)]
#[allow(unused)]
/// Constructs mock verifying keys for a program without the overhead of synthesis.
pub fn mock_verifying_keys(
    program: &Program<Testnet3>,
) -> Vec<(Identifier<Testnet3>, (VerifyingKey<Testnet3>, Certificate<Testnet3>))> {
    program
        .functions()
        .iter()
        .map(|(identifier, _)| (*identifier, (VerifyingKey::mock(), Certificate::mock(identifier).unwrap())))
        .collect_vec()
}
