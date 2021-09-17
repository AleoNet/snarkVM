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

use snarkvm_dpc::prelude::*;
use snarkvm_ledger::{ledger::*, prelude::*, testnet1::*, testnet2::*};
use snarkvm_utilities::ToBytes;

use rand::thread_rng;
use std::{
    fs::File,
    io::{Result as IoResult, Write},
    path::Path,
    str::FromStr,
};

pub fn generate<N: Network>(recipient: Address<N::DPC>, value: u64) -> Result<(Vec<u8>, Vec<u8>), DPCError> {
    let rng = &mut thread_rng();

    // TODO (howardwu): Deprecate this in favor of a simple struct with 2 Merkle trees.
    let temporary_ledger = Ledger::<N, MemDb>::new(None, Block {
        previous_block_hash: BlockHash([0u8; 32]),
        header: BlockHeader {
            transactions_root: MerkleRoot([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork::default(),
        },
        transactions: Transactions::new(),
    })
    .unwrap();

    let amount = AleoAmount::from_bytes(value as i64);
    let state = StateTransition::new_coinbase(recipient, amount, rng)?;
    let authorization = DPC::<N::DPC>::authorize(&vec![], &state, rng)?;
    let transaction = DPC::<N::DPC>::execute(authorization, state.executables(), &temporary_ledger, rng)?;

    let transaction_bytes = transaction.to_bytes_le()?;
    println!("transaction size - {}\n", transaction_bytes.len());

    // Add genesis transaction to block.
    let mut transactions = Transactions::new();
    transactions.push(transaction);

    // Create a genesis header.
    let genesis_header = BlockHeader::new_genesis::<N::DPC, _>(&transactions, &mut thread_rng())?;
    assert!(genesis_header.is_genesis());
    println!("block header size - {}\n", BlockHeader::size());

    println!(
        "block size - {}\n",
        transaction_bytes.len() + BlockHeader::size() + 1 /* variable_length_integer for number of transaction */
    );

    Ok((genesis_header.to_bytes_le()?.to_vec(), transaction_bytes))
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

            let (genesis_header, transaction) = generate::<Testnet1>(recipient, balance).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        "testnet2" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let balance = args[3].parse::<u64>().unwrap();
            let genesis_header_file = &args[4];
            let transaction_file = &args[5];

            let (genesis_header, transaction) = generate::<Testnet2>(recipient, balance).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        _ => panic!("Invalid parameters"),
    };
}
