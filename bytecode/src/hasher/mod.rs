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

/// An enum containing any possible hasher gadget for a program.
#[derive(Clone)]
pub enum Hasher<P: Program> {
    Pedersen64(Pedersen64<P>),
    Pedersen128(Pedersen128<P>),
    Pedersen256(Pedersen256<P>),
    Pedersen512(Pedersen512<P>),
    Pedersen1024(Pedersen1024<P>),
}

impl<P: Program> Hasher<P> {
    /// Creates a new `Hasher` for a given opcode.
    pub fn new(name: &str) -> Self {
        match name {
            "ped64" => Self::Pedersen64(Pedersen64::new()),
            "ped128" => Self::Pedersen128(Pedersen128::new()),
            "ped256" => Self::Pedersen256(Pedersen256::new()),
            "ped512" => Self::Pedersen512(Pedersen512::new()),
            "ped1024" => Self::Pedersen1024(Pedersen1024::new()),
            _ => P::halt(format!("Hasher \'{name}\' is not implemented")),
        }
    }

    /// Hash the given `value` with the corresponding hasher.
    pub fn hash(&self, value: Literal<P::Environment>) -> Literal<P::Environment> {
        match self {
            Self::Pedersen64(h) => h.hash(value),
            Self::Pedersen128(h) => h.hash(value),
            Self::Pedersen256(h) => h.hash(value),
            Self::Pedersen512(h) => h.hash(value),
            Self::Pedersen1024(h) => h.hash(value),
        }
    }
}
