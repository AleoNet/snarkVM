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

use snarkvm_console::{account::PrivateKey, network::Testnet3, prelude::*};
use snarkvm_synthesizer::{Block, ConsensusMemory, ConsensusStore, VM};

use rand::thread_rng;
use std::{
    fs::File,
    io::{Result as IoResult, Write},
    path::Path,
};

pub fn generate<N: Network>(private_key: PrivateKey<N>) -> Result<Vec<u8>> {
    // Initialize the consensus store.
    let store = ConsensusStore::<N, ConsensusMemory<N>>::open(None)?;
    // Initialize the VM.
    let vm = VM::from(store)?;
    // Create a genesis block.
    let genesis_block = Block::genesis(&vm, &private_key, &mut thread_rng())?;
    // assert!(genesis_block.verify(&VM::<N>::new()?));
    assert!(genesis_block.is_genesis());
    assert!(genesis_block.header().is_genesis());

    println!("\n{}\n", serde_json::to_string_pretty(&genesis_block)?);

    println!("Genesis block size - {}\n", genesis_block.to_bytes_le()?.len());
    println!("Genesis block header size - {}\n", genesis_block.header().to_bytes_le()?.len());

    genesis_block.to_bytes_le()
}

pub fn store<P: AsRef<Path>>(path: P, bytes: &[u8]) -> IoResult<()> {
    let mut file = File::create(path)?;
    file.write_all(bytes)?;
    Ok(())
}

#[allow(clippy::match_single_binding)]
pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        println!("Invalid number of arguments. Given: {} - Required: 3", args.len() - 1);
        return;
    }

    match args[1].as_str() {
        "testnet3" => {
            let private_key = PrivateKey::from_str(&args[2]).unwrap();
            let genesis_file = &args[3];

            let genesis_block = generate::<Testnet3>(private_key).unwrap();
            store(genesis_file, &genesis_block).unwrap();
        }
        _ => panic!("Invalid network"),
    };
}
