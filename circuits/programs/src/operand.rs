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

use crate::{Immediate, Memory, Register};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;
use nom::{branch::alt, combinator::map};

#[derive(Clone)]
pub enum Operand<M: Memory> {
    Immediate(Immediate<M::Environment>),
    Register(Register),
}

impl<M: Memory> Operand<M> {
    /// Returns `true` if the value type is a register.
    pub(super) fn is_register(&self) -> bool {
        matches!(self, Self::Register(..))
    }

    /// Returns the value from a register, otherwise passes the loaded value through.
    pub(super) fn to_value(&self) -> Immediate<M::Environment> {
        match self {
            Self::Immediate(value) => value.clone(),
            Self::Register(register) => M::load(register),
        }
    }
}

impl<M: Memory> From<Immediate<M::Environment>> for Operand<M> {
    fn from(immediate: Immediate<M::Environment>) -> Operand<M> {
        Operand::Immediate(immediate)
    }
}

impl<M: Memory> From<&Immediate<M::Environment>> for Operand<M> {
    fn from(immediate: &Immediate<M::Environment>) -> Operand<M> {
        Operand::from(immediate.clone())
    }
}

impl<M: Memory> From<Register> for Operand<M> {
    fn from(register: Register) -> Operand<M> {
        Operand::Register(register)
    }
}

impl<M: Memory> From<&Register> for Operand<M> {
    fn from(register: &Register) -> Operand<M> {
        Operand::from(register.clone())
    }
}

impl<M: Memory> Parser for Operand<M> {
    type Output = Operand<M>;

    /// Parses a string into an operand.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        alt((
            map(Immediate::parse, |immediate| Self::Immediate(immediate)),
            map(Register::parse, |register| Self::Register(register)),
        ))(string)
    }
}

impl<M: Memory> fmt::Display for Operand<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Immediate(immediate) => immediate.fmt(f),
            Self::Register(register) => register.fmt(f),
        }
    }
}
