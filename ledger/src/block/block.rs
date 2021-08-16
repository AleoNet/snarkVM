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

use crate::{BlockHeader, BlockScheme, Transactions};
use snarkvm_dpc::TransactionScheme;
use snarkvm_utilities::{FromBytes, ToBytes};

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
