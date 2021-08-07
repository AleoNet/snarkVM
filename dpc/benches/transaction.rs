// Copyright (C) 2019-2021 Aleo Systems Inc.
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

#[macro_use]
extern crate criterion;

use snarkvm_dpc::{prelude::*, testnet1::*, testnet2::*};
use snarkvm_ledger::{ledger::*, prelude::*};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use criterion::Criterion;
use rand::thread_rng;
use std::sync::Arc;

fn coinbase_transaction<C: Parameters>(
    dpc: &DPC<C>,
    ledger: &Ledger<C, MemDb>,
    recipient: Address<C>,
    value: u64,
) -> Result<Transaction<C>, DPCError> {
    let rng = &mut thread_rng();

    // Generate accounts.
    let genesis_account = Account::new(rng)?;

    // Generate input records having as address the genesis address.
    let private_keys = vec![genesis_account.private_key.clone(); C::NUM_INPUT_RECORDS];

    let mut joint_serial_numbers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
    let mut input_records = Vec::with_capacity(C::NUM_INPUT_RECORDS);
    for i in 0..C::NUM_INPUT_RECORDS {
        let input_record = Record::new_noop_input(&dpc.noop_program, genesis_account.address, rng)?;

        let (sn, _) = input_record.to_serial_number(&private_keys[i])?;
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn]?);

        input_records.push(input_record);
    }

    // Construct the output records.
    let mut output_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
    output_records.push(Record::new_output(
        &dpc.noop_program,
        recipient,
        false,
        value,
        Payload::default(),
        C::NUM_INPUT_RECORDS as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);
    output_records.push(Record::new_noop_output(
        &dpc.noop_program,
        recipient,
        (C::NUM_INPUT_RECORDS + 1) as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);

    let authorization = dpc.authorize(&private_keys, input_records, output_records, None, rng)?;

    // Fetch the noop circuit ID.
    let noop_circuit_id = dpc
        .noop_program
        .find_circuit_by_index(0)
        .ok_or(DPCError::MissingNoopCircuit)?
        .circuit_id();

    // Construct the executable.
    let noop = Executable::Noop(Arc::new(dpc.noop_program.clone()), *noop_circuit_id);
    let executables = vec![noop.clone(), noop.clone(), noop.clone(), noop];

    // Generate the transaction.
    let transaction = dpc.execute(&private_keys, authorization, executables, ledger, rng)?;

    Ok(transaction)
}

fn testnet1_coinbase_transaction(c: &mut Criterion) {
    // TODO (howardwu): Deprecate this in favor of a simple struct with 2 Merkle trees.
    let ledger = Ledger::<Testnet1Parameters, MemDb>::new(None, Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            merkle_root_hash: MerkleRootHash([0u8; 32]),
            pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
            time: 0,
            difficulty_target: 0xFFFF_FFFF_FFFF_FFFF_u64,
            nonce: 0,
            proof: ProofOfSuccinctWork([0u8; 771]),
        },
        transactions: Transactions::new(),
    })
    .unwrap();

    let dpc = DPC::<Testnet1Parameters>::load(false).unwrap();

    let recipient_account = Account::new(&mut thread_rng()).unwrap();

    c.bench_function("testnet1_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = coinbase_transaction(&dpc, &ledger, recipient_account.address, 100).unwrap();
        })
    });
}

fn testnet2_coinbase_transaction(c: &mut Criterion) {
    // TODO (howardwu): Deprecate this in favor of a simple struct with 2 Merkle trees.
    let ledger = Ledger::<Testnet2Parameters, MemDb>::new(None, Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            merkle_root_hash: MerkleRootHash([0u8; 32]),
            pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
            time: 0,
            difficulty_target: 0xFFFF_FFFF_FFFF_FFFF_u64,
            nonce: 0,
            proof: ProofOfSuccinctWork([0u8; 771]),
        },
        transactions: Transactions::new(),
    })
    .unwrap();

    let dpc = DPC::<Testnet2Parameters>::load(false).unwrap();

    let recipient_account = Account::new(&mut thread_rng()).unwrap();

    c.bench_function("testnet2_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = coinbase_transaction(&dpc, &ledger, recipient_account.address, 100).unwrap();
        })
    });
}

criterion_group! {
    name = transaction;
    config = Criterion::default().sample_size(10);
    targets = testnet1_coinbase_transaction, testnet2_coinbase_transaction
}

criterion_main!(transaction);
