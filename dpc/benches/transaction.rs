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

#[macro_use]
extern crate criterion;

use snarkvm_dpc::{prelude::*, testnet1::*, testnet2::*};
use snarkvm_ledger::{ledger::*, prelude::*};

use criterion::Criterion;
use rand::thread_rng;
use std::sync::Arc;

fn coinbase_transaction<C: Parameters>(
    ledger: &Ledger<C, MemDb>,
    recipient: Address<C>,
    value: u64,
) -> Result<Transaction<C>, DPCError> {
    let rng = &mut thread_rng();

    let amount = AleoAmount::from_bytes(value as i64);
    let state = StateTransition::new_coinbase(recipient, amount, rng)?;
    let authorization = DPC::<C>::authorize(&vec![], &state, rng)?;
    let transaction = DPC::<C>::execute(&vec![], authorization, state.executables(), ledger, rng)?;

    Ok(transaction)
}

fn testnet1_coinbase_transaction(c: &mut Criterion) {
    // TODO (howardwu): Deprecate this in favor of a simple struct with 2 Merkle trees.
    let ledger = Ledger::<Testnet1Parameters, MemDb>::new(None, Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRootHash([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork([0u8; 771]),
        },
        transactions: Transactions::new(),
    })
    .unwrap();

    let recipient_account = Account::new(&mut thread_rng()).unwrap();

    c.bench_function("testnet1_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = coinbase_transaction(&ledger, recipient_account.address, 100).unwrap();
        })
    });
}

fn testnet2_coinbase_transaction(c: &mut Criterion) {
    // TODO (howardwu): Deprecate this in favor of a simple struct with 2 Merkle trees.
    let ledger = Ledger::<Testnet2Parameters, MemDb>::new(None, Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRootHash([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork([0u8; 771]),
        },
        transactions: Transactions::new(),
    })
    .unwrap();

    let recipient_account = Account::new(&mut thread_rng()).unwrap();

    c.bench_function("testnet2_coinbase_transaction", move |b| {
        b.iter(|| {
            let _transaction = coinbase_transaction(&ledger, recipient_account.address, 100).unwrap();
        })
    });
}

criterion_group! {
    name = transaction;
    config = Criterion::default().sample_size(10);
    targets = testnet1_coinbase_transaction, testnet2_coinbase_transaction
}

criterion_main!(transaction);
