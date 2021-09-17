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

use crate::{AleoAmount, Memo, Network};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::hash::Hash;

pub trait TransactionScheme<N: Network>: Clone + Eq + FromBytes + ToBytes + Send + Sync {
    type Digest: Clone + Eq + Hash + FromBytes + ToBytes;
    type EncryptedRecord: Clone + Eq + FromBytes + ToBytes;

    /// Returns the network ID in the transaction.
    fn network_id(&self) -> u16;

    /// Returns the old serial numbers.
    fn serial_numbers(&self) -> &[N::SerialNumber];

    /// Returns the new commitments.
    fn commitments(&self) -> &[N::RecordCommitment];

    /// Returns the value balance in the transaction.
    fn value_balance(&self) -> &AleoAmount;

    /// Returns the memorandum.
    fn memo(&self) -> &Memo<N>;

    /// Returns the ledger digest.
    fn ledger_digest(&self) -> &Self::Digest;

    /// Returns the inner circuit ID.
    fn inner_circuit_id(&self) -> &N::InnerCircuitID;

    /// Returns the encrypted records
    fn encrypted_records(&self) -> &[Self::EncryptedRecord];

    /// Returns the transaction ID.
    fn to_transaction_id(&self) -> Result<N::TransactionID>;
}
