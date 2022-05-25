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

use snarkvm_dpc::{prelude::*, testnet1::*};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use std::sync::atomic::AtomicBool;
use time::OffsetDateTime;

#[test]
fn test_testnet1_input_circuit_id_sanity_check() {
    let expected_input_circuit_id =
        "ic19n30tdzyvk0hhuuuxkxpy3wyk20jmxpjsuk96j4a0r7pacjpe7fnqwp78yw29yw7l6gn88xh2gpsqv7qe97".to_string();
    let candidate_input_circuit_id = <Testnet1 as Network>::input_circuit_id().to_string();
    assert_eq!(expected_input_circuit_id, candidate_input_circuit_id);
}

#[test]
fn test_testnet1_output_circuit_id_sanity_check() {
    let expected_output_circuit_id =
        "oc1q3uf400qh8ytmss7283ygztkrmm8lw7czjclrkge7gtdhgf0qj48f4y262wpsxd3f4axktma8dtszjr03mg".to_string();
    let candidate_output_circuit_id = <Testnet1 as Network>::output_circuit_id().to_string();
    assert_eq!(expected_output_circuit_id, candidate_output_circuit_id);
}

#[test]
fn dpc_testnet1_integration_test() {
    let mut rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

    let mut ledger = Ledger::<Testnet1>::new().unwrap();
    assert_eq!(ledger.latest_block_height(), 0);
    assert_eq!(ledger.latest_block_hash(), Testnet1::genesis_block().hash());
    assert_eq!(&ledger.latest_block().unwrap(), Testnet1::genesis_block());
    assert_eq!((*ledger.latest_block_transactions().unwrap()).len(), 1);
    assert_eq!(
        ledger.latest_block().unwrap().to_coinbase_transaction().unwrap(),
        (*ledger.latest_block_transactions().unwrap())[0]
    );

    // Construct the previous block hash and new block height.
    let previous_block = ledger.latest_block().unwrap();
    let previous_block_hash = previous_block.hash();
    let block_height = previous_block.header().height() + 1;
    assert_eq!(block_height, 1);

    // Construct the new block transactions.
    let recipient = Account::new(rng);
    let amount = Block::<Testnet1>::block_reward(block_height);
    let (coinbase_transaction, coinbase_record) =
        Transaction::<Testnet1>::new_coinbase(recipient.address(), amount, true, rng).unwrap();
    {
        // Check that the coinbase transaction is serialized and deserialized correctly.
        let transaction_bytes = coinbase_transaction.to_bytes_le().unwrap();
        let recovered_transaction = Transaction::<Testnet1>::read_le(&transaction_bytes[..]).unwrap();
        assert_eq!(coinbase_transaction, recovered_transaction);

        // Check that coinbase record can be decrypted from the transaction.
        let encrypted_record = coinbase_transaction.ciphertexts().next().unwrap();
        let view_key = ViewKey::from_private_key(recipient.private_key());
        let decrypted_record = Record::decrypt(&view_key.into(), encrypted_record).unwrap();
        assert_eq!(decrypted_record.owner(), recipient.address());
        assert_eq!(decrypted_record.value(), Block::<Testnet1>::block_reward(1));
    }
    let transactions = Transactions::from(&[coinbase_transaction]).unwrap();

    let previous_ledger_root = ledger.latest_ledger_root();
    let timestamp = OffsetDateTime::now_utc().unix_timestamp();
    let difficulty_target =
        Blocks::<Testnet1>::compute_difficulty_target(previous_block.header(), timestamp, block_height);
    let cumulative_weight = previous_block.cumulative_weight().saturating_add((u64::MAX / difficulty_target) as u128);

    // Construct the block template.
    let template = BlockTemplate::new(
        previous_block_hash,
        block_height,
        timestamp,
        difficulty_target,
        cumulative_weight,
        previous_ledger_root,
        transactions,
        coinbase_record,
    );

    // Construct the new block.
    let block = Block::mine(&template, &AtomicBool::new(false), &mut rng).unwrap();

    ledger.add_next_block(&block).unwrap();
    assert_eq!(ledger.latest_block_height(), 1);
}
