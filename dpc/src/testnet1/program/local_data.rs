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

use crate::{
    testnet1::{Testnet1Components, Transaction},
    Record,
    TransactionScheme,
};
use snarkvm_algorithms::{commitment_tree::CommitmentMerkleTree, prelude::*};

/// Stores local data required to produce program proofs.
pub struct LocalData<C: Testnet1Components> {
    // Old records and serial numbers
    pub old_records: Vec<Record<C>>,
    pub old_serial_numbers: Vec<<C::AccountSignature as SignatureScheme>::PublicKey>,

    // New records
    pub new_records: Vec<Record<C>>,

    // Commitment to the above information.
    pub local_data_merkle_tree: CommitmentMerkleTree<C::LocalDataCommitment, C::LocalDataCRH>,
    pub local_data_commitment_randomizers: Vec<<C::LocalDataCommitment as CommitmentScheme>::Randomness>,

    pub memorandum: <Transaction<C> as TransactionScheme>::Memorandum,
    pub network_id: u8,
}
