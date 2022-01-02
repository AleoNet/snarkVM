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

use snarkvm_utilities::{error, FromBytes, ToBytes};

use serde::{Deserialize, Serialize};
use std::io::{Read, Result as IoResult, Write};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionType {
    Noop,
    Insert,
    Update,
    Remove,
    DoubleInsert,
    DoubleRemove,
    Join,
    Split,
    Full,
}

impl FunctionType {
    /// Return the id of the function type.
    pub fn id(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Insert => 1,
            Self::Update => 2,
            Self::Remove => 3,
            Self::DoubleInsert => 4,
            Self::DoubleRemove => 5,
            Self::Join => 6,
            Self::Split => 7,
            Self::Full => 8,
        }
    }

    /// Return a function type given an id.
    pub fn from_id(id: u8) -> IoResult<Self> {
        Ok(match id {
            0 => Self::Noop,
            1 => Self::Insert,
            2 => Self::Update,
            3 => Self::Remove,
            4 => Self::DoubleInsert,
            5 => Self::DoubleRemove,
            6 => Self::Join,
            7 => Self::Split,
            8 => Self::Full,
            _ => return Err(error("Invalid function type id")),
        })
    }

    /// Returns the number of expected input records in a transition.
    pub fn input_count(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Insert => 0,
            Self::Update => 1,
            Self::Remove => 1,
            Self::DoubleInsert => 0,
            Self::DoubleRemove => 2,
            Self::Join => 2,
            Self::Split => 1,
            Self::Full => 2,
        }
    }

    /// Returns the number of expected output records in a transition.
    pub fn output_count(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Insert => 1,
            Self::Update => 1,
            Self::Remove => 0,
            Self::DoubleInsert => 2,
            Self::DoubleRemove => 0,
            Self::Join => 1,
            Self::Split => 2,
            Self::Full => 2,
        }
    }
}

impl FromBytes for FunctionType {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let function_type_id: u8 = FromBytes::read_le(&mut reader)?;
        Self::from_id(function_type_id)
    }
}

impl ToBytes for FunctionType {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.id().write_le(&mut writer)
    }
}
