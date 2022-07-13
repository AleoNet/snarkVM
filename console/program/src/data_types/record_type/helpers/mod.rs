// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use snarkvm_console_network::prelude::*;

/// A helper enum for the visibility of an entry.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum PublicOrPrivate {
    Public,
    Private,
}

impl PublicOrPrivate {
    /// Returns `true` if the entry is public.
    pub const fn is_public(&self) -> bool {
        matches!(self, PublicOrPrivate::Public)
    }

    /// Returns `true` if the entry is private.
    pub const fn is_private(&self) -> bool {
        matches!(self, PublicOrPrivate::Private)
    }
}

impl FromBytes for PublicOrPrivate {
    /// Reads the visibility from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the indicator for the visibility.
        match u8::read_le(&mut reader)? == 1 {
            true => Ok(PublicOrPrivate::Private),
            false => Ok(PublicOrPrivate::Public),
        }
    }
}

impl ToBytes for PublicOrPrivate {
    /// Writes the visibility to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the indicator for the visibility.
        (*self as u8).write_le(&mut writer)
    }
}

impl Debug for PublicOrPrivate {
    /// Prints the visibility as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for PublicOrPrivate {
    /// Prints the visibility as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            PublicOrPrivate::Public => write!(f, "public"),
            PublicOrPrivate::Private => write!(f, "private"),
        }
    }
}
