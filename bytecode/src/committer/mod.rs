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

use crate::Program;
use snarkvm_circuits::Literal;

mod ped64;
use ped64::*;

mod ped128;
use ped128::*;

mod ped256;
use ped256::*;

mod ped512;
use ped512::*;

mod ped1024;
use ped1024::*;

/// An enum containing any possible committer gadget for a program.
#[derive(Clone)]
pub enum Committer<P: Program> {
    Pedersen64(Pedersen64<P>),
    Pedersen128(Pedersen128<P>),
    Pedersen256(Pedersen256<P>),
    Pedersen512(Pedersen512<P>),
    Pedersen1024(Pedersen1024<P>),
}

impl<P: Program> Committer<P> {
    /// Creates a new `Committer` for a given opcode.
    pub fn new(name: &str) -> Self {
        match name {
            "commit.ped64" => Self::Pedersen64(Pedersen64::default()),
            "commit.ped128" => Self::Pedersen128(Pedersen128::default()),
            "commit.ped256" => Self::Pedersen256(Pedersen256::default()),
            "commit.ped512" => Self::Pedersen512(Pedersen512::default()),
            "commit.ped1024" => Self::Pedersen1024(Pedersen1024::default()),
            _ => P::halt(format!("Committer \'{name}\' is not implemented")),
        }
    }

    /// Commit to the given `value` and `randomness` with the corresponding committer.
    pub fn commit(
        &self,
        value: Literal<P::Environment>,
        randomness: Literal<P::Environment>,
    ) -> Literal<P::Environment> {
        match self {
            Self::Pedersen64(h) => h.commit(value, randomness),
            Self::Pedersen128(h) => h.commit(value, randomness),
            Self::Pedersen256(h) => h.commit(value, randomness),
            Self::Pedersen512(h) => h.commit(value, randomness),
            Self::Pedersen1024(h) => h.commit(value, randomness),
        }
    }
}
