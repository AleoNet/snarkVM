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

use crate::{ledger::*, prelude::*};
use snarkvm_dpc::{prelude::*, testnet2::Testnet2};
use snarkvm_parameters::{testnet2::Transaction1, traits::Genesis};

use rand::thread_rng;

#[test]
fn test_new_ledger_with_genesis_block() {
    let transactions =
        BlockTransactions::from(&[Transaction::<Testnet2>::from_bytes_le(&Transaction1::load_bytes()).unwrap()]);
    let header = BlockHeader::<Testnet2>::new_genesis(&transactions, &mut thread_rng()).unwrap();
    let genesis_block = Block {
        previous_hash: Default::default(),
        header,
        transactions,
    };

    let ledger = Ledger::<Testnet2, MemDb>::new(None, genesis_block.clone()).unwrap();
    let genesis_block_hash = ledger.get_block_hash(0).unwrap();

    assert_eq!(ledger.block_height(), 0);
    assert_eq!(ledger.latest_block().unwrap(), genesis_block.clone());
    assert_eq!(ledger.get_block_hash(0).unwrap(), genesis_block_hash.clone());
    assert_eq!(ledger.get_block(&genesis_block_hash).unwrap(), genesis_block);
    assert_eq!(ledger.get_block_number(&genesis_block_hash).unwrap(), 0);
    assert_eq!(ledger.contains_block_hash(&genesis_block_hash), true);

    assert!(ledger.get_block(&Default::default()).is_err());
}

#[test]
fn test_ledger_duplicate_transactions() {
    let transaction = Transaction::<Testnet2>::from_bytes_le(&Transaction1::load_bytes()).unwrap();
    let transactions = BlockTransactions::from(&[transaction.clone(), transaction]);

    let genesis_block = Block {
        previous_hash: Default::default(),
        header: BlockHeader::new_genesis(&transactions, &mut thread_rng()).unwrap(),
        transactions,
    };

    assert!(Ledger::<Testnet2, MemDb>::new(None, genesis_block.clone()).is_err());
}
