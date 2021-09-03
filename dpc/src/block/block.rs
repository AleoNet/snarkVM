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
    traits::{BlockScheme, TransactionScheme},
    BlockError,
    BlockHeader,
    Transactions,
};
use snarkvm_utilities::{to_bytes_le, variable_length_integer::variable_length_integer, FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Block<T: TransactionScheme> {
    /// First `HEADER_SIZE` bytes of the block as defined by the encoding used by "block" messages.
    pub header: BlockHeader,
    /// The block transactions.
    pub transactions: Transactions<T>,
}

impl<T: TransactionScheme> BlockScheme for Block<T> {
    type BlockHeader = BlockHeader;
    type Transaction = T;

    /// Returns the header.
    fn header(&self) -> &Self::BlockHeader {
        &self.header
    }

    /// Returns the transactions.
    fn transactions(&self) -> &[Self::Transaction] {
        self.transactions.as_slice()
    }
}

impl<T: TransactionScheme> ToBytes for Block<T> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.header.write_le(&mut writer)?;
        self.transactions.write_le(&mut writer)
    }
}

impl<T: TransactionScheme> FromBytes for Block<T> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let header: BlockHeader = FromBytes::read_le(&mut reader)?;
        let transactions: Transactions<T> = FromBytes::read_le(&mut reader)?;

        Ok(Self { header, transactions })
    }
}

impl<T: TransactionScheme> Block<T> {
    pub fn serialize(&self) -> Result<Vec<u8>, BlockError> {
        let mut serialization = vec![];
        serialization.extend(&self.header.serialize().to_vec());
        serialization.extend(&variable_length_integer(self.transactions.len() as u64));

        for transaction in self.transactions.iter() {
            serialization.extend(to_bytes_le![transaction]?)
        }

        Ok(serialization)
    }

    pub fn deserialize(bytes: &[u8]) -> Result<Self, BlockError> {
        const HEADER_SIZE: usize = BlockHeader::size();
        let (header_bytes, transactions_bytes) = bytes.split_at(HEADER_SIZE);

        let mut header_array = [0u8; HEADER_SIZE];
        header_array.copy_from_slice(&header_bytes[0..HEADER_SIZE]);
        let header = BlockHeader::deserialize(&header_array);

        let transactions: Transactions<T> = FromBytes::read_le(transactions_bytes)?;

        Ok(Block { header, transactions })
    }
}
