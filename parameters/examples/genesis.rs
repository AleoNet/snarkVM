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

use snarkvm_dpc::{prelude::*, testnet1::*, testnet2::*};
use snarkvm_utilities::ToBytes;

use anyhow::Result;
use rand::thread_rng;
use std::{
    fs::File,
    io::{Result as IoResult, Write},
    path::Path,
    str::FromStr,
};

pub fn generate<N: Network>(recipient: Address<N>) -> Result<Vec<u8>> {
    // Create a genesis block.
    let genesis_block = Block::<N>::new_genesis(recipient, &mut thread_rng())?;
    assert!(genesis_block.is_valid());
    assert!(genesis_block.is_genesis());
    assert!(genesis_block.header().is_genesis());
    assert!(genesis_block.to_coinbase_transaction()?.is_valid());

    println!("\n{}\n", serde_json::to_string_pretty(&genesis_block)?);

    println!("Genesis block size - {}\n", genesis_block.to_bytes_le()?.len());
    println!("Genesis block header size - {}\n", genesis_block.header().to_bytes_le()?.len());
    println!("Genesis block header proof size - {}\n", genesis_block.header().proof().to_bytes_le()?.len());
    println!("Genesis coinbase transaction size - {}\n", genesis_block.to_coinbase_transaction()?.to_bytes_le()?.len());
    println!(
        "Genesis coinbase transition size - {}\n",
        genesis_block.to_coinbase_transaction()?.transitions()[0].to_bytes_le()?.len()
    );

    genesis_block.to_bytes_le()
}

pub fn store<P: AsRef<Path>>(path: P, bytes: &[u8]) -> IoResult<()> {
    let mut file = File::create(path)?;
    file.write_all(bytes)?;
    Ok(())
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        println!("Invalid number of arguments. Given: {} - Required: 3", args.len() - 1);
        return;
    }

    match args[1].as_str() {
        "testnet1" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let genesis_file = &args[3];

            let genesis_block = generate::<Testnet1>(recipient).unwrap();
            store(genesis_file, &genesis_block).unwrap();
        }
        "testnet2" => {
            let recipient = Address::from_str(&args[2]).unwrap();
            let genesis_file = &args[3];

            let genesis_block = generate::<Testnet2>(recipient).unwrap();
            store(genesis_file, &genesis_block).unwrap();
        }
        _ => panic!("Invalid network"),
    };
}
