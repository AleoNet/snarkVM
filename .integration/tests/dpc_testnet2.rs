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

use std::sync::atomic::AtomicBool;

use snarkvm_dpc::{prelude::*, testnet2::*};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use time::OffsetDateTime;

#[test]
fn test_testnet2_inner_circuit_id_sanity_check() {
    let expected_inner_circuit_id =
        "ic1zqxh2kd4u7ll9lzj4dmwj0tzmcn0kjc68hv2x47l7kwvsz7nf4u65vfr5z3uemup9l5x2zuyjv4sqf86sfs".to_string();
    let candidate_inner_circuit_id = <Testnet2 as Network>::inner_circuit_id().to_string();
    assert_eq!(expected_inner_circuit_id, candidate_inner_circuit_id);
}

#[test]
fn dpc_testnet2_integration_test() {
    let mut rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

    let mut ledger = Ledger::<Testnet2>::new().unwrap();
    assert_eq!(ledger.latest_block_height(), 0);
    assert_eq!(ledger.latest_block_hash(), Testnet2::genesis_block().hash());
    assert_eq!(&ledger.latest_block().unwrap(), Testnet2::genesis_block());
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
    let amount = Block::<Testnet2>::block_reward(block_height);
    let (coinbase_transaction, coinbase_record) =
        Transaction::<Testnet2>::new_coinbase(recipient.address(), amount, true, rng).unwrap();
    {
        // Check that the coinbase transaction is serialized and deserialized correctly.
        let transaction_bytes = coinbase_transaction.to_bytes_le().unwrap();
        let recovered_transaction = Transaction::<Testnet2>::read_le(&transaction_bytes[..]).unwrap();
        assert_eq!(coinbase_transaction, recovered_transaction);

        // Check that coinbase record can be decrypted from the transaction.
        let encrypted_record = coinbase_transaction.ciphertexts().next().unwrap();
        let view_key = ViewKey::from_private_key(recipient.private_key());
        let decrypted_record = Record::decrypt(&view_key.into(), encrypted_record).unwrap();
        assert_eq!(decrypted_record.owner(), recipient.address());
        assert_eq!(decrypted_record.value(), Block::<Testnet2>::block_reward(1));
    }
    let transactions = Transactions::from(&[coinbase_transaction]).unwrap();

    let previous_ledger_root = ledger.latest_ledger_root();
    let timestamp = OffsetDateTime::now_utc().unix_timestamp();
    let difficulty_target =
        Blocks::<Testnet2>::compute_difficulty_target(previous_block.header(), timestamp, block_height);
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

// #[test]
// fn test_record_size() {
//     use std::str::FromStr;
//
//     let ledger = Ledger::<Testnet2>::new().unwrap();
//
//     // Initialize a new account.
//     let private_key =
//         PrivateKey::<Testnet2>::from_str("APrivateKey1zkp8cC4jgHEBnbtu3xxs1Ndja2EMizcvTRDq5Nikdkukg1p").unwrap();
//     let account = Account::from(private_key.clone());
//     let view_key = account.view_key();
//
//     // Mine the next block.
//     let block = ledger.latest_block().unwrap();
//     println!("block: {}", block.hash());
//
//     // Craft the transaction variables.
//     let coinbase_transaction = &block.transactions()[0];
//     let candidate_records = coinbase_transaction.to_decrypted_records(view_key);
//     assert_eq!(candidate_records.len(), 1); // Excludes dummy records upon decryption.
//
//     let candidate_record = candidate_records.first().unwrap();
//     assert_eq!(
//         "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
//         candidate_record.owner().to_string()
//     );
//     assert_eq!(
//         AleoAmount(Testnet2::ALEO_STARTING_SUPPLY_IN_CREDITS * 1_000_000),
//         candidate_record.value()
//     );
//     assert_eq!(vec![0u8; 128], candidate_record.payload().to_bytes_le().unwrap());
//     assert_eq!(Testnet2::noop_program_id(), &candidate_record.program_id());
// }
