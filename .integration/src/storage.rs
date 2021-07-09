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

use crate::Ledger;
use snarkvm_algorithms::traits::merkle_tree::LoadableMerkleParameters;
use snarkvm_dpc::{
    block::Block,
    traits::{LedgerScheme, Storage, TransactionScheme},
    TransactionError,
};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::{thread_rng, Rng};
use std::{
    io::{Read, Result as IoResult, Write},
    sync::Arc,
};

pub fn random_storage_path() -> String {
    let random_path: usize = thread_rng().gen();
    format!("./test_db-{}", random_path)
}

// Initialize a test blockchain given genesis attributes
pub fn initialize_test_blockchain<T: TransactionScheme, P: LoadableMerkleParameters, S: Storage>(
    parameters: Arc<P>,
    genesis_block: Block<T>,
) -> Ledger<T, P, S> {
    let mut path = std::env::temp_dir();
    path.push(random_storage_path());

    Ledger::<T, P, S>::new(Some(&path), parameters, genesis_block).unwrap()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestTx;

impl TransactionScheme for TestTx {
    type Commitment = [u8; 32];
    type Digest = [u8; 32];
    type EncryptedRecord = [u8; 32];
    type InnerCircuitID = [u8; 32];
    type LocalDataRoot = [u8; 32];
    type Memorandum = [u8; 32];
    type ProgramCommitment = [u8; 32];
    type SerialNumber = [u8; 32];
    type Signature = [u8; 32];
    type ValueBalance = i64;

    fn transaction_id(&self) -> Result<[u8; 32], TransactionError> {
        Ok([0u8; 32])
    }

    fn network_id(&self) -> u8 {
        0
    }

    fn ledger_digest(&self) -> &Self::Digest {
        &[0u8; 32]
    }

    fn inner_circuit_id(&self) -> &Self::InnerCircuitID {
        &[0u8; 32]
    }

    fn old_serial_numbers(&self) -> &[Self::SerialNumber] {
        &[[0u8; 32]; 2]
    }

    fn new_commitments(&self) -> &[Self::Commitment] {
        &[[0u8; 32]; 2]
    }

    fn program_commitment(&self) -> &Self::ProgramCommitment {
        &[0u8; 32]
    }

    fn local_data_root(&self) -> &Self::LocalDataRoot {
        &[0u8; 32]
    }

    fn value_balance(&self) -> i64 {
        0
    }

    fn memorandum(&self) -> &Self::Memorandum {
        &[0u8; 32]
    }

    fn signatures(&self) -> &[Self::Signature] {
        &[[0u8; 32]; 2]
    }

    fn encrypted_records(&self) -> &[Self::EncryptedRecord] {
        &[[0u8; 32]; 2]
    }

    fn size(&self) -> usize {
        0
    }
}

impl ToBytes for TestTx {
    #[inline]
    fn write_le<W: Write>(&self, mut _writer: W) -> IoResult<()> {
        Ok(())
    }
}

impl FromBytes for TestTx {
    #[inline]
    fn read<R: Read>(mut _reader: R) -> IoResult<Self> {
        Ok(Self)
    }
}
