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

use crate::Network;
use snarkvm_fields::{ConstraintFieldError, PrimeField, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::{
    fmt::{
        Display,
        Formatter,
        {self},
    },
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    ops::Deref,
};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Memo<N: Network>(Vec<u8>, PhantomData<N>);

impl<N: Network> Memo<N> {
    pub fn new(memo: &[u8]) -> Result<Self> {
        assert_eq!(memo.len(), N::MEMO_SIZE_IN_BYTES);
        Ok(Self::read_le(memo)?)
    }

    pub fn size() -> usize {
        N::MEMO_SIZE_IN_BYTES
    }
}

impl<N: Network> FromBytes for Memo<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut buffer = vec![0u8; N::MEMO_SIZE_IN_BYTES];
        reader.read_exact(&mut buffer)?;
        Ok(Self(buffer, PhantomData))
    }
}

impl<N: Network> ToBytes for Memo<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<N: Network, F: PrimeField> ToConstraintField<F> for Memo<N> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.0.to_field_elements()
    }
}

impl<N: Network> Default for Memo<N> {
    fn default() -> Self {
        Self(vec![0u8; N::MEMO_SIZE_IN_BYTES], PhantomData)
    }
}

impl<N: Network> Display for Memo<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<N: Network> Deref for Memo<N> {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
