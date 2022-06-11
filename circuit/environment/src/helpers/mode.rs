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

use crate::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    Constant,
    Public,
    Private,
}

impl Mode {
    /// Returns `true` if the mode is a constant.
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant)
    }

    /// Returns `true` if the mode is public.
    pub const fn is_public(&self) -> bool {
        matches!(self, Self::Public)
    }

    /// Returns `true` if the mode is private.
    pub const fn is_private(&self) -> bool {
        matches!(self, Self::Private)
    }

    /// Parses a string into a mode.
    #[inline]
    pub fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(tag("constant"), |_| Self::Constant),
            map(tag("public"), |_| Self::Public),
            map(tag("private"), |_| Self::Private),
        ))(string)
    }

    /// A static helper to deduce the mode from a list of modes.
    #[inline]
    pub fn combine<M: IntoIterator<Item = Mode>>(starting_mode: Mode, modes: M) -> Mode {
        // Initialize the current mode.
        let mut current_mode = starting_mode;
        // Intuition: Start from `Mode::Constant`, and see if one needs to lift to `Mode::Public` or `Mode::Private`.
        //   - If `current_mode == Mode::Constant`, then `current_mode = next_mode`.
        //   - If `current_mode == Mode::Public` && `next_mode == Mode::Private`, then `current_mode = next_mode`.
        //   - Otherwise, do nothing.
        for next_mode in modes {
            // Check if the current mode matches the next mode.
            if !current_mode.is_private() && current_mode != next_mode {
                match (current_mode, next_mode) {
                    (Mode::Constant, Mode::Public)
                    | (Mode::Constant, Mode::Private)
                    | (Mode::Public, Mode::Private) => current_mode = next_mode,
                    (_, _) => (), // Do nothing.
                }
            }
        }
        current_mode
    }
}

impl IntoIterator for Mode {
    type IntoIter = std::iter::Once<Self>;
    type Item = Mode;

    /// Returns an iterator over the mode.
    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self)
    }
}

impl FromStr for Mode {
    type Err = Error;

    /// Parses a string into a mode.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl Display for Mode {
    /// Formats the mode as a lowercase string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Constant => write!(f, "constant"),
            Self::Public => write!(f, "public"),
            Self::Private => write!(f, "private"),
        }
    }
}

impl ToBytes for Mode {
    /// Writes the mode to the writer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (*self as u8).write_le(&mut writer)
    }
}

impl FromBytes for Mode {
    /// Reads the mode from the reader.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mode = u8::read_le(&mut reader)?;
        match mode {
            0 => Ok(Self::Constant),
            1 => Ok(Self::Public),
            2 => Ok(Self::Private),
            _ => Err(error("Invalid mode")),
        }
    }
}
