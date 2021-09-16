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

use crate::{ledger::*, prelude::*, testnet2::Testnet2};
use snarkvm_dpc::{parameters::testnet2::Testnet2Parameters, Transaction};
use snarkvm_parameters::{testnet2::Transaction1, traits::Genesis};

use rand::thread_rng;

#[test]
fn test_new_ledger_with_genesis_block() {
    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: MaskedMerkleRoot([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork::default(),
        },
        transactions: Transactions::new(),
    };

    // If the underlying hash function is changed, this expected block hash will need to be updated.
    let expected_genesis_block_hash = BlockHeaderHash([
        63, 138, 252, 86, 177, 15, 96, 131, 45, 199, 133, 61, 241, 76, 206, 159, 100, 110, 164, 142, 79, 11, 11, 157,
        173, 145, 155, 126, 14, 240, 235, 13,
    ]);

    let ledger = Ledger::<Testnet2, Testnet2Parameters, MemDb>::new(None, genesis_block.clone()).unwrap();

    assert_eq!(ledger.block_height(), 0);
    assert_eq!(ledger.latest_block().unwrap(), genesis_block.clone());
    assert_eq!(ledger.get_block_hash(0).unwrap(), expected_genesis_block_hash.clone());
    assert_eq!(ledger.get_block(&expected_genesis_block_hash).unwrap(), genesis_block);
    assert_eq!(ledger.get_block_number(&expected_genesis_block_hash).unwrap(), 0);
    assert_eq!(ledger.contains_block_hash(&expected_genesis_block_hash), true);

    assert!(ledger.get_block(&BlockHeaderHash([0u8; 32])).is_err());
}

#[test]
fn test_ledger_duplicate_transactions() {
    let transaction = Transaction::<Testnet2Parameters>::from_bytes_le(&Transaction1::load_bytes()).unwrap();
    let transactions = Transactions::from(&[transaction.clone(), transaction]);

    let block_header = BlockHeader::new_genesis::<_, Testnet2Parameters, _>(&transactions, &mut thread_rng()).unwrap();

    let genesis_block = Block {
        header: block_header,
        transactions,
    };

    assert!(Ledger::<Testnet2, Testnet2Parameters, MemDb>::new(None, genesis_block.clone()).is_err());
}
