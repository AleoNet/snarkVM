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

use crate::variable_length::*;
use snarkvm_circuits::{Environment, Parser, ParserResult};

use core::{fmt, marker::PhantomData, ops};
use nom::{
    bytes::complete::tag,
    character::complete::one_of,
    combinator::{map_res, recognize},
    multi::many1,
};
use snarkvm_utilities::{FromBytes, ToBytes};
use std::{
    fs::read,
    io::{Read, Result as IoResult, Write},
};

#[derive(Copy, Clone, Eq, Hash, PartialEq)]
pub struct Register<E: Environment>(u64, PhantomData<E>);

impl<E: Environment> Register<E> {
    /// Returns a new instance of a register.
    pub(crate) fn new(locator: u64) -> Register<E> {
        Self(locator, PhantomData)
    }
}

impl<E: Environment> Parser for Register<E> {
    type Environment = E;

    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "r"
    }

    /// Parses a string into a register.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the register keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the locator from the string.
        let (string, locator) =
            map_res(recognize(many1(one_of("0123456789"))), |locator: &str| locator.parse::<u64>())(string)?;

        Ok((string, Register::new(locator)))
    }
}

impl<E: Environment> fmt::Display for Register<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", Self::type_name(), self.0)
    }
}

impl<E: Environment> ops::Deref for Register<E> {
    type Target = u64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Environment> FromBytes for Register<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self::new(read_variable_length_integer(&mut reader)?))
    }
}

impl<E: Environment> ToBytes for Register<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
    where
        Self: Sized,
    {
        variable_length_integer(self.0).write_le(&mut writer)
    }
}
