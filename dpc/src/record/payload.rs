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

use std::io::{Read, Result as IoResult, Write};

pub const PAYLOAD_SIZE: usize = 128;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Payload([u8; PAYLOAD_SIZE]);

impl Payload {
    pub fn to_bytes(&self) -> &[u8] {
        &self.0[..]
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut payload = [0u8; PAYLOAD_SIZE];
        payload.copy_from_slice(&bytes);

        Self(payload)
    }

    pub fn size(&self) -> usize {
        self.0.len()
    }
}

impl ToBytes for Payload {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl FromBytes for Payload {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?))
    }
}

impl Default for Payload {
    fn default() -> Self {
        Self([0u8; PAYLOAD_SIZE])
    }
}
