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

use crate::prelude::*;
use snarkvm_dpc::parameters::testnet2::Testnet2Parameters;

#[test]
fn test_new_ledger_with_genesis_block() {
    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            merkle_root_hash: MerkleRootHash([0u8; 32]),
            pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
            proof: ProofOfSuccinctWork([0u8; 972]),
            time: 0,
            difficulty_target: 0xFFFF_FFFF_FFFF_FFFF_u64,
            nonce: 0,
        },
        transactions: Transactions::new(),
    };

    // If the underlying hash function is changed, this expected block hash will need to be updated.
    let expected_genesis_block_hash = BlockHeaderHash([
        215, 251, 137, 243, 59, 18, 138, 175, 132, 222, 67, 161, 9, 37, 39, 228, 77, 110, 32, 174, 55, 65, 58, 177,
        122, 117, 87, 96, 102, 156, 1, 182,
    ]);

    let ledger = Ledger::<Testnet2Parameters, MemDb>::new(None, genesis_block.clone()).unwrap();

    assert_eq!(ledger.block_height(), 1);
    assert_eq!(ledger.latest_block().unwrap(), genesis_block.clone());
    assert_eq!(ledger.get_block_hash(1).unwrap(), expected_genesis_block_hash.clone());
    assert_eq!(ledger.get_block(&expected_genesis_block_hash).unwrap(), genesis_block);
    assert_eq!(ledger.contains_block_hash(&expected_genesis_block_hash), true);

    assert!(ledger.get_block_hash(0).is_err());
    assert!(ledger.get_block(&BlockHeaderHash([0u8; 32])).is_err());
}
