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

use snarkvm_dpc::{prelude::*, testnet1::*, testnet2::*};
use snarkvm_ledger::{
    ledger::*,
    posw::{txids_to_roots, PoswMarlin},
    prelude::*,
};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use rand::thread_rng;
use std::{
    fs::File,
    io::{Result as IoResult, Write},
    ops::Deref,
    path::Path,
    str::FromStr,
    sync::Arc,
};

pub fn generate<C: Parameters>(recipient: Address<C>, value: u64) -> Result<(Vec<u8>, Vec<u8>), DPCError> {
    let rng = &mut thread_rng();

    // TODO (howardwu): Deprecate this in favor of a simple struct with 2 Merkle trees.
    let temporary_ledger = Ledger::<C, MemDb>::new(None, Block {
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

    let dpc = DPC::<C>::load(false)?;

    // Generate accounts.
    let genesis_account = Account::new(rng)?;

    // Generate input records having as address the genesis address.
    let private_keys = vec![genesis_account.private_key.clone(); C::NUM_INPUT_RECORDS];

    let mut joint_serial_numbers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
    let mut input_records = Vec::with_capacity(C::NUM_INPUT_RECORDS);
    for i in 0..C::NUM_INPUT_RECORDS {
        let input_record = Record::new_noop_input(dpc.noop_program.deref(), genesis_account.address, rng)?;

        let (sn, _) = input_record.to_serial_number(&private_keys[i])?;
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn]?);

        input_records.push(input_record);
    }

    // Construct the output records.
    let mut output_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
    output_records.push(Record::new_output(
        dpc.noop_program.deref(),
        recipient,
        false,
        value,
        Payload::default(),
        C::NUM_INPUT_RECORDS as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);
    output_records.push(Record::new_noop_output(
        dpc.noop_program.deref(),
        recipient,
        (C::NUM_INPUT_RECORDS + 1) as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);

    // Offline execution to generate a transaction authorization.
    let authorization = dpc.authorize(&private_keys, input_records, output_records, None, rng)?;

    // Construct the executable.
    let noop = Executable::Noop(Arc::new(dpc.noop_program.clone()));
    let executables = vec![noop.clone(), noop.clone(), noop.clone(), noop];

    let transaction = dpc.execute(&private_keys, authorization, executables, &temporary_ledger, rng)?;

    let transaction_bytes = transaction.to_bytes_le()?;
    let transaction_size = transaction_bytes.len();
    println!("transaction size - {}\n", transaction_size);

    // Add genesis transaction to block.
    let mut transactions = Transactions::new();
    transactions.push(transaction);

    // Construct the root hashes from the txids.
    let txids = transactions.to_transaction_ids()?;
    let (merkle_root_hash, pedersen_merkle_root_hash, subroots) = txids_to_roots(&txids);

    // Construct the initial block attributes.
    let time = 0;
    let initial_difficulty_target = 0xFFFF_FFFF_FFFF_FFFF_u64;
    let max_nonce = u32::MAX;

    // Mine the block.
    let posw = PoswMarlin::load().expect("could not instantiate the posw miner");
    let (nonce, proof) = posw
        .mine(&subroots, initial_difficulty_target, &mut thread_rng(), max_nonce)
        .unwrap();

    // Create a genesis header.
    let genesis_header = BlockHeader {
        previous_block_hash: BlockHeaderHash([0u8; 32]),
        merkle_root_hash,
        pedersen_merkle_root_hash,
        time,
        difficulty_target: initial_difficulty_target,
        nonce,
        proof: proof.into(),
    };
    assert!(genesis_header.is_genesis());
    println!("block header size - {}\n", BlockHeader::size());

    println!(
        "block size - {}\n",
        transaction_size + BlockHeader::size() + 1 /* variable_length_integer for number of transaction */
    );

    Ok((genesis_header.serialize().to_vec(), transaction_bytes))
}

pub fn store<P: AsRef<Path>>(path: P, bytes: &[u8]) -> IoResult<()> {
    let mut file = File::create(path)?;
    file.write_all(&bytes)?;

    Ok(())
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 6 {
        println!("Invalid number of arguments. Given: {} - Required: 5", args.len() - 1);
        return;
    }

    match args[1].as_str() {
        "testnet1" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let balance = args[3].parse::<u64>().unwrap();
            let genesis_header_file = &args[4];
            let transaction_file = &args[5];

            let (genesis_header, transaction) = generate::<Testnet1Parameters>(recipient, balance).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        "testnet2" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let balance = args[3].parse::<u64>().unwrap();
            let genesis_header_file = &args[4];
            let transaction_file = &args[5];

            let (genesis_header, transaction) = generate::<Testnet2Parameters>(recipient, balance).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        _ => panic!("Invalid parameters"),
    };
}
