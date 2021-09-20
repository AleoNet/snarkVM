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

use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use rand::{CryptoRng, Rng};

pub trait BlockScheme: Clone + Eq + FromBytes + ToBytes + Send + Sync {
    type BlockHash: Clone + Eq + FromBytes + ToBytes;
    type Header: Clone + Eq + FromBytes + ToBytes;
    type Transactions: Clone + Eq + FromBytes + ToBytes;

    type Commitment: Clone + Eq + FromBytes + ToBytes;
    type SerialNumber: Clone + Eq + FromBytes + ToBytes;

    type Address: Clone + Eq + FromBytes + ToBytes;

    /// Initializes a new genesis block, with a coinbase transaction for the given recipient.
    fn new_genesis<R: Rng + CryptoRng>(recipient: Self::Address, rng: &mut R) -> Result<Self>;

    /// Returns `true` if the block is well-formed.
    fn is_valid(&self) -> bool;

    /// Returns the previous block hash.
    fn previous_hash(&self) -> &Self::BlockHash;

    /// Returns the header.
    fn header(&self) -> &Self::Header;

    /// Returns the transactions.
    fn transactions(&self) -> &Self::Transactions;

    /// Returns the block height.
    fn height(&self) -> u32;

    /// Returns the hash of this block.
    fn to_block_hash(&self) -> Result<Self::BlockHash>;

    /// Returns the commitments in the block, by constructing a flattened list of commitments from all transactions.
    fn to_commitments(&self) -> Result<Vec<Self::Commitment>>;

    /// Returns the serial numbers in the block, by constructing a flattened list of serial numbers from all transactions.
    fn to_serial_numbers(&self) -> Result<Vec<Self::SerialNumber>>;
}
