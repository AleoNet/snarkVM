// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use snarkvm_circuits::helpers::integers::IntegerType;

use anyhow::{anyhow, Result};
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::recognize,
    multi::{many0, many1},
    sequence::terminated,
    IResult,
};

pub struct Integer<I: IntegerType>(I);

impl<I: IntegerType> Integer<I> {
    pub fn new(input: &'static str) -> Result<Self> {
        let (remainder, (value, type_)) = Self::parse(input)?;

        let value: String = value.into_iter().collect();

        match type_ == I::type_name() && remainder.is_empty() {
            true => Ok(Self(value.parse::<I>()?)),
            false => Err(anyhow!("Failed to parse the {} value {}", I::type_name(), input)),
        }
    }

    pub fn to_value(&self) -> I {
        self.0
    }

    fn parse(input: &str) -> IResult<&str, (Vec<char>, &str)> {
        let (type_, digits) = many1(terminated(one_of("0123456789"), many0(char('_'))))(input)?;
        let (remainder, type_) = tag(I::type_name())(type_)?;
        Ok((remainder, (digits, type_)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u8() {
        type I = u8;
        assert_eq!(5u8, Integer::<I>::new("5u8").unwrap().to_value());
        assert_eq!(5u8, Integer::<I>::new("5_u8").unwrap().to_value());
        assert_eq!(15u8, Integer::<I>::new("1_5_u8").unwrap().to_value());
    }

    #[test]
    fn test_malformed_integer() {
        assert!(Integer::<u8>::new("5u_8").is_err());
    }
}
