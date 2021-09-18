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
    let genesis_block = Block {
        previous_block_hash: BlockHash([0u8; 32]),
        header: BlockHeader {
            transactions_root: MerkleRoot([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new_genesis(),
            proof: ProofOfSuccinctWork::default(),
        },
        transactions: Transactions::new(),
    };

    // If the underlying hash function is changed, this expected block hash will need to be updated.
    let expected_genesis_block_hash = BlockHash([
        197, 96, 131, 8, 176, 90, 158, 53, 59, 89, 40, 231, 1, 173, 161, 190, 41, 41, 127, 88, 136, 45, 109, 15, 192,
        178, 217, 198, 27, 174, 226, 2,
    ]);

    let ledger = Ledger::<Testnet2, MemDb>::new(None, genesis_block.clone()).unwrap();

    assert_eq!(ledger.block_height(), 0);
    assert_eq!(ledger.latest_block().unwrap(), genesis_block.clone());
    assert_eq!(ledger.get_block_hash(0).unwrap(), expected_genesis_block_hash.clone());
    assert_eq!(ledger.get_block(&expected_genesis_block_hash).unwrap(), genesis_block);
    assert_eq!(ledger.get_block_number(&expected_genesis_block_hash).unwrap(), 0);
    assert_eq!(ledger.contains_block_hash(&expected_genesis_block_hash), true);

    assert!(ledger.get_block(&BlockHash([0u8; 32])).is_err());
}

#[test]
fn test_ledger_duplicate_transactions() {
    let transaction = Transaction::<Testnet2>::from_bytes_le(&Transaction1::load_bytes()).unwrap();
    let transactions = Transactions::from(&[transaction.clone(), transaction]);

    let block_header = BlockHeader::new_genesis(&transactions, &mut thread_rng()).unwrap();

    let genesis_block = Block {
        previous_block_hash: BlockHash([0u8; 32]),
        header: block_header,
        transactions,
    };

    assert!(Ledger::<Testnet2, MemDb>::new(None, genesis_block.clone()).is_err());
}
