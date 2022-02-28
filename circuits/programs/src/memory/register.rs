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

use crate::{Immediate, Memory};
use snarkvm_circuits::{Parser, ParserResult};

use core::fmt;

#[derive(Copy, Clone, Eq, Hash, PartialEq)]
pub struct Register(u64);

impl Register {
    /// Returns a new instance of a register.
    pub(super) fn new(locator: u64) -> Register {
        Self(locator)
    }
}

// impl Parser for Register {
//     type Output = Register;
//
//     /// Parses a string into a register.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self::Output> {
//         alt((
//             map(BaseField::parse, |base| Self::BaseField(base)),
//             map(Boolean::parse, |boolean| Self::Boolean(boolean)),
//             map(Affine::parse, |group| Self::Group(group)),
//         ))(string)
//     }
// }

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}
