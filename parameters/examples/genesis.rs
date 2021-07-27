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

mod utils;
use utils::{initialize_test_blockchain, MemDb};

use snarkvm_algorithms::CRH;
use snarkvm_dpc::{
    merkle_root,
    testnet1::parameters::*,
    Account,
    AccountScheme,
    Address,
    Block,
    BlockHeader,
    BlockHeaderHash,
    DPCError,
    DPCScheme,
    MerkleRootHash,
    Parameters,
    Payload,
    PedersenMerkleRootHash,
    ProgramScheme,
    ProofOfSuccinctWork,
    Record,
    Transactions,
};
use snarkvm_posw::{txids_to_roots, PoswMarlin};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use rand::thread_rng;
use std::{
    fs::File,
    io::{Result as IoResult, Write},
    path::Path,
    str::FromStr,
};

pub fn generate(recipient: &Address<Testnet1Parameters>, value: u64) -> Result<(Vec<u8>, Vec<u8>), DPCError> {
    let rng = &mut thread_rng();

    let dpc = Testnet1DPC::load(false)?;

    let ledger = initialize_test_blockchain::<Testnet1Parameters, MemDb>(Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            merkle_root_hash: MerkleRootHash([0u8; 32]),
            pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
            time: 0,
            difficulty_target: 0x07FF_FFFF_FFFF_FFFF_u64,
            nonce: 0,
            proof: ProofOfSuccinctWork([0u8; 972]),
        },
        transactions: Transactions::new(),
    });

    // Generate accounts.
    let genesis_account = Account::new(rng)?;

    // Generate input records having as address the genesis address.
    let old_private_keys = vec![genesis_account.private_key.clone(); Testnet1Parameters::NUM_INPUT_RECORDS];

    let mut joint_serial_numbers = Vec::with_capacity(Testnet1Parameters::NUM_INPUT_RECORDS);
    let mut old_records = Vec::with_capacity(Testnet1Parameters::NUM_INPUT_RECORDS);
    for i in 0..Testnet1Parameters::NUM_INPUT_RECORDS {
        let old_record = Record::new(
            genesis_account.address.clone(),
            true, // The input record is a noop.
            0,
            Payload::default(),
            dpc.noop_program.id(),
            dpc.noop_program.id(),
            Testnet1Parameters::serial_number_nonce_crh().hash(&[64u8 + (i as u8); 1])?,
            rng,
        )?;

        let (sn, _) = old_record.to_serial_number(&old_private_keys[i])?;
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn]?);

        old_records.push(old_record);
    }

    // Construct the new records.
    let mut new_records = Vec::with_capacity(Testnet1Parameters::NUM_OUTPUT_RECORDS);
    new_records.push(Record::new_full(
        recipient.clone(),
        false,
        value,
        Payload::default(),
        dpc.noop_program.id(),
        dpc.noop_program.id(),
        Testnet1Parameters::NUM_INPUT_RECORDS as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);
    new_records.push(Record::new_full(
        recipient.clone(),
        true,
        0,
        Payload::default(),
        dpc.noop_program.id(),
        dpc.noop_program.id(),
        (Testnet1Parameters::NUM_INPUT_RECORDS + 1) as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);

    // Offline execution to generate a DPC transaction kernel.
    let kernel = dpc.execute_offline_phase(&old_private_keys, old_records, new_records, [0; 64], rng)?;

    // Generate the program proofs
    let mut program_proofs = Vec::with_capacity(Testnet1Parameters::NUM_TOTAL_RECORDS);
    for i in 0..Testnet1Parameters::NUM_TOTAL_RECORDS {
        program_proofs.push(dpc.noop_program.execute(&kernel.into_local_data(), i as u8, rng)?);
    }

    let (new_records, transaction) =
        dpc.execute_online_phase(&old_private_keys, kernel, program_proofs, &ledger, rng)?;

    let transaction_bytes = transaction.to_bytes_le()?;
    let size = transaction_bytes.len();
    println!("transaction size - {}\n", size);

    for (i, record) in new_records.iter().enumerate() {
        let record_bytes = to_bytes_le![record]?;
        println!("record {}: {:?}\n", i, hex::encode(record_bytes));
    }

    // Add genesis transaction to block.
    let mut transactions = Transactions::new();
    transactions.push(transaction);

    let txids = transactions.to_transaction_ids()?;

    let (merkle_root_hash, pedersen_merkle_root_hash, subroots) = txids_to_roots(&txids);

    // Mine the block.
    let time = 0; // Utc::now().timestamp();
    let initial_difficulty_target = 0x07FF_FFFF_FFFF_FFFF_u64;
    let max_nonce = u32::MAX;

    let posw = PoswMarlin::load().expect("could not instantiate the miner");
    let (nonce, proof) = posw
        .mine(&subroots, difficulty_target, &mut thread_rng(), max_nonce)
        .unwrap();

    // Establish the merkle root hash of the transactions.
    let mut merkle_root_bytes = [0u8; 32];
    merkle_root_bytes[..].copy_from_slice(&merkle_root(&transactions.to_transaction_ids()?));

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

    // // Create a genesis block.
    // let genesis_block = Block {
    //     header: genesis_header.clone(),
    //     transactions: Transactions::new(),
    // };

    // let ledger =
    //     initialize_test_blockchain::<Testnet1Parameters, Transaction<Testnet1Parameters>, MemDb>(genesis_block);

    Ok((genesis_header.serialize().to_vec(), transaction_bytes))
}

pub fn store<P: AsRef<Path>>(path: P, bytes: &[u8]) -> IoResult<()> {
    let mut file = File::create(path)?;
    file.write_all(&bytes)?;

    Ok(())
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 5 {
        println!("Invalid number of arguments. Given: {} - Required: 4", args.len() - 1);
        return;
    }

    let recipient = &Address::<Testnet1Parameters>::from_str(&args[1]).unwrap();
    let balance = args[2].parse::<u64>().unwrap();
    let genesis_header_file = &args[3];
    let transaction_file = &args[4];

    let (genesis_header, transaction) = generate(recipient, balance).unwrap();
    store(genesis_header_file, &genesis_header).unwrap();
    store(transaction_file, &transaction).unwrap();
}
