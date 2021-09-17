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

use crate::Parameters;
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
pub struct Memo<C: Parameters>(Vec<u8>, PhantomData<C>);

impl<C: Parameters> Memo<C> {
    pub fn new(memo: &[u8]) -> Result<Self> {
        assert_eq!(memo.len(), C::MEMO_SIZE_IN_BYTES);
        Ok(Self::read_le(memo)?)
    }

    pub fn size() -> usize {
        C::MEMO_SIZE_IN_BYTES
    }
}

impl<C: Parameters> FromBytes for Memo<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut buffer = vec![0u8; C::MEMO_SIZE_IN_BYTES];
        reader.read_exact(&mut buffer)?;
        Ok(Self(buffer, PhantomData))
    }
}

impl<C: Parameters> ToBytes for Memo<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<C: Parameters, F: PrimeField> ToConstraintField<F> for Memo<C> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.0.to_field_elements()
    }
}

impl<C: Parameters> Default for Memo<C> {
    fn default() -> Self {
        Self(vec![0u8; C::MEMO_SIZE_IN_BYTES], PhantomData)
    }
}

impl<C: Parameters> Display for Memo<C> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<C: Parameters> Deref for Memo<C> {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
