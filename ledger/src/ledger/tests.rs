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
use snarkvm_dpc::parameters::testnet2::Testnet2Parameters;

#[test]
fn test_new_ledger_with_genesis_block() {
    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRootHash([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork::default(),
        },
        transactions: Transactions::new(),
    };

    // If the underlying hash function is changed, this expected block hash will need to be updated.
    let expected_genesis_block_hash = BlockHeaderHash([
        181, 154, 143, 117, 166, 9, 195, 238, 250, 143, 179, 197, 156, 162, 245, 242, 247, 127, 213, 209, 196, 45, 80,
        225, 227, 100, 54, 108, 86, 6, 59, 93,
    ]);

    let ledger = Ledger::<Testnet2Parameters, MemDb>::new(None, genesis_block.clone()).unwrap();

    assert_eq!(ledger.block_height(), 0);
    assert_eq!(ledger.latest_block().unwrap(), genesis_block.clone());
    assert_eq!(ledger.get_block_hash(0).unwrap(), expected_genesis_block_hash.clone());
    assert_eq!(ledger.get_block(&expected_genesis_block_hash).unwrap(), genesis_block);
    assert_eq!(ledger.get_block_number(&expected_genesis_block_hash).unwrap(), 0);
    assert_eq!(ledger.contains_block_hash(&expected_genesis_block_hash), true);

    assert!(ledger.get_block(&BlockHeaderHash([0u8; 32])).is_err());
}
