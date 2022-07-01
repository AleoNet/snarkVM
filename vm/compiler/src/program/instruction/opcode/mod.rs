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

use console::network::prelude::*;

/// The `Opcode` enum stores the mnemonic for the instruction.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Opcode {
    /// The opcode is for a literal operation (i.e. `add`).
    Literal(&'static str),
    /// The opcode is for a call operation (i.e. `call`).
    Call,
    /// The opcode is for a cast operation (i.e. `cast`).
    Cast,
    /// The opcode is for a commit operation (i.e. `commit.psd4`).
    Commit(&'static str),
    /// The opcode is for a hash operation (i.e. `hash.psd4`).
    Hash(&'static str),
}

impl Deref for Opcode {
    type Target = &'static str;

    /// Returns the opcode as a string.
    fn deref(&self) -> &Self::Target {
        match self {
            Opcode::Literal(opcode) => opcode,
            Opcode::Call => &"call",
            Opcode::Cast => &"cast",
            Opcode::Commit(opcode) => opcode,
            Opcode::Hash(opcode) => opcode,
        }
    }
}

impl Debug for Opcode {
    /// Prints the opcode as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Opcode {
    /// Prints the opcode as a string, i.e. `add`.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // write!(f, "{}", *self)
        match self {
            Self::Literal(opcode) => write!(f, "{opcode}"),
            Self::Call => write!(f, "{}", self.deref()),
            Self::Cast => write!(f, "{}", self.deref()),
            Self::Commit(opcode) => write!(f, "{opcode}"),
            Self::Hash(opcode) => write!(f, "{opcode}"),
        }
    }
}
