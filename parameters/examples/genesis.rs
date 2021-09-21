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
use snarkvm_utilities::ToBytes;

use rand::thread_rng;
use std::{
    fs::File,
    io::{Result as IoResult, Write},
    path::Path,
    str::FromStr,
};

pub fn generate<N: Network>(recipient: Address<N>) -> Result<(Vec<u8>, Vec<u8>), DPCError> {
    // Create a genesis block.
    let genesis_block = Block::<N>::new_genesis(recipient, &mut thread_rng()).unwrap();
    let transaction = genesis_block.to_coinbase_transaction().unwrap();

    let transaction_bytes = transaction.to_bytes_le()?;
    println!("transaction size - {}\n", transaction_bytes.len());

    // Create a genesis header.
    let genesis_header = genesis_block.header();
    assert!(genesis_header.is_genesis());
    println!("block header size - {}\n", BlockHeader::<N>::size());

    println!(
        "block size - {}\n",
        transaction_bytes.len() + BlockHeader::<N>::size() + 1 /* variable_length_integer for number of transaction */
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
    if args.len() < 5 {
        println!("Invalid number of arguments. Given: {} - Required: 4", args.len() - 1);
        return;
    }

    match args[1].as_str() {
        "testnet1" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let genesis_header_file = &args[3];
            let transaction_file = &args[4];

            let (genesis_header, transaction) = generate::<Testnet1>(recipient).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        "testnet2" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let genesis_header_file = &args[3];
            let transaction_file = &args[4];

            let (genesis_header, transaction) = generate::<Testnet2>(recipient).unwrap();
            store(genesis_header_file, &genesis_header).unwrap();
            store(transaction_file, &transaction).unwrap();
        }
        _ => panic!("Invalid network"),
    };
}
