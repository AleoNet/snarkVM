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

use snarkvm_algorithms::CRH;
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
    path::Path,
    str::FromStr,
};

pub fn generate<C: Parameters>(recipient: &Address<C>, value: u64) -> Result<(Vec<u8>, Vec<u8>), DPCError> {
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
    let mut old_records = Vec::with_capacity(C::NUM_INPUT_RECORDS);
    for i in 0..C::NUM_INPUT_RECORDS {
        let old_record = Record::new(
            &dpc.noop_program,
            genesis_account.address.clone(),
            true, // The input record is a noop.
            0,
            Payload::default(),
            C::serial_number_nonce_crh().hash(&[64u8 + (i as u8); 1])?,
            rng,
        )?;

        let (sn, _) = old_record.to_serial_number(&private_keys[i])?;
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn]?);

        old_records.push(old_record);
    }

    // Construct the new records.
    let mut new_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
    new_records.push(Record::new_full(
        &dpc.noop_program,
        recipient.clone(),
        false,
        value,
        Payload::default(),
        C::NUM_INPUT_RECORDS as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);
    new_records.push(Record::new_full(
        &dpc.noop_program,
        recipient.clone(),
        true,
        0,
        Payload::default(),
        (C::NUM_INPUT_RECORDS + 1) as u8,
        joint_serial_numbers.clone(),
        rng,
    )?);

    // Offline execution to generate a transaction authorization.
    let authorization = dpc.authorize(&private_keys, old_records, new_records, None, rng)?;

    // Generate the local data.
    let local_data = authorization.to_local_data(rng)?;

    // Generate the program proofs
    let mut program_proofs = Vec::with_capacity(C::NUM_TOTAL_RECORDS);
    for i in 0..C::NUM_TOTAL_RECORDS {
        let public_variables = ProgramPublicVariables::new(local_data.root(), i as u8);
        program_proofs.push(
            dpc.noop_program
                .execute(0, &public_variables, &NoopPrivateVariables::new())?,
        );
    }

    let transaction = dpc.execute(
        &private_keys,
        authorization,
        &local_data,
        program_proofs,
        &temporary_ledger,
        rng,
    )?;

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

    println!("block size - {}\n", transaction_size + BlockHeader::size());

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
            let recipient = &Address::from_str(&args[2]).unwrap();
            let balance = args[3].parse::<u64>().unwrap();
            let genesis_header_file = &args[4];
            let transaction_file = &args[5];

            let (genesis_header, transaction) = generate::<Testnet1Parameters>(recipient, balance).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        "testnet2" => {
            let recipient = &Address::from_str(&args[2]).unwrap();
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
