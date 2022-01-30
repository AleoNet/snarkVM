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

use anyhow::{anyhow, Result};
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::recognize,
    multi::{many0, many1},
    sequence::terminated,
    IResult,
};

pub struct Integer(u8);

impl Integer {
    pub fn new(input: &'static str) -> Result<Self> {
        let (remainder, (value, type_)) = Self::parse(input)?;
        match type_ == "u8" && remainder.is_empty() {
            true => Ok(Self(value.replace("_", "").parse::<u8>()?)),
            false => Err(anyhow!("Failed to parse the u8 value {}", input)),
        }
    }

    pub fn to_value(&self) -> u8 {
        self.0
    }

    fn parse(input: &str) -> IResult<&str, (&str, &str)> {
        let (type_, value) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)?;
        let (remainder, type_) = tag("u8")(type_)?;
        Ok((remainder, (value, type_)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u8() {
        assert_eq!(5u8, Integer::new("5u8").unwrap().to_value());
        assert_eq!(5u8, Integer::new("5_u8").unwrap().to_value());
        assert_eq!(15u8, Integer::new("1_5_u8").unwrap().to_value());
    }

    #[test]
    fn test_malformed_integer() {
        assert!(Integer::new("5u_8").is_err());
    }
}
