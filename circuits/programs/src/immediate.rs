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

use snarkvm_circuits::{Affine, BaseField, Boolean, Environment, Parser, ParserResult};

use core::fmt;
use nom::{branch::alt, bytes::complete::tag, combinator::map};

#[derive(Clone)]
pub enum Immediate<E: Environment> {
    BaseField(BaseField<E>),
    Boolean(Boolean<E>),
    // Group(Affine<E>),
}

impl<E: Environment> Parser for Immediate<E> {
    type Output = Immediate<E>;

    /// Parses a string into an immediate.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self::Output> {
        alt((
            map(BaseField::parse, |base| Self::BaseField(base)),
            map(Boolean::parse, |boolean| Self::Boolean(boolean)),
        ))(string)
    }
}

impl<E: Environment> fmt::Display for Immediate<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::BaseField(base) => base.fmt(f),
            Self::Boolean(boolean) => boolean.fmt(f),
        }
    }
}
