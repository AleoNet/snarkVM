// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use console::network::prelude::*;

/// The `Opcode` enum stores the mnemonic for the instruction.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Opcode {
    /// The opcode is for a assert operation (i.e. `assert`).
    Assert(&'static str),
    /// The opcode is for a call operation (i.e. `call`).
    Call,
    /// The opcode is for a cast operation (i.e. `cast`).
    Cast,
    /// The opcode is for a finalize command (i.e. `increment`).
    Command(&'static str),
    /// The opcode is for a commit operation (i.e. `commit.psd4`).
    Commit(&'static str),
    /// The opcode is for a remove operation (i.e. `delete`).
    Delete,
    /// The opcode is for a finalize operation (i.e. `finalize`).
    Finalize(&'static str),
    /// The opcode is for a hash operation (i.e. `hash.psd4`).
    Hash(&'static str),
    /// The opcode is for an index operation (i.e. `index`).
    Index,
    /// The opcode for an 'is' operation (i.e. `is.eq`).
    Is(&'static str),
    /// The opcode is for a `length` operation (i.e. `length`).
    Length,
    /// The opcode is for a literal operation (i.e. `add`).
    Literal(&'static str),
    /// The opcode is for a push operation (i.e. `push`).
    Push,
}

impl Deref for Opcode {
    type Target = &'static str;

    /// Returns the opcode as a string.
    fn deref(&self) -> &Self::Target {
        match self {
            Opcode::Assert(opcode) => opcode,
            Opcode::Call => &"call",
            Opcode::Cast => &"cast",
            Opcode::Command(opcode) => opcode,
            Opcode::Commit(opcode) => opcode,
            Opcode::Delete => &"delete",
            Opcode::Finalize(opcode) => opcode,
            Opcode::Get => &"get",
            Opcode::Hash(opcode) => opcode,
            Opcode::Index => &"index",
            Opcode::Is(opcode) => opcode,
            Opcode::Length => &"length",
            Opcode::Literal(opcode) => opcode,
            Opcode::Push => &"push",
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
        match self {
            Self::Assert(opcode) => write!(f, "{opcode}"),
            Self::Call => write!(f, "{}", self.deref()),
            Self::Cast => write!(f, "{}", self.deref()),
            Self::Command(opcode) => write!(f, "{opcode}"),
            Self::Commit(opcode) => write!(f, "{opcode}"),
            Self::Delete => write!(f, "{}", self.deref()),
            Self::Finalize(opcode) => write!(f, "{opcode}"),
            Self::Get => write!(f, "{}", self.deref()),
            Self::Hash(opcode) => write!(f, "{opcode}"),
            Self::Index => write!(f, "{}", self.deref()),
            Self::Is(opcode) => write!(f, "{opcode}"),
            Self::Length => write!(f, "{}", self.deref()),
            Self::Literal(opcode) => write!(f, "{opcode}"),
            Self::Push => write!(f, "{}", self.deref()),
        }
    }
}
