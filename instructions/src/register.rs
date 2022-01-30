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

pub struct Register(u64);

impl Register {
    pub fn new(input: &'static str) -> Result<Self> {
        let (input, value) = Self::parse(input)?;
        Ok(Self(value.replace("_", "").parse::<u64>()?))
    }

    pub fn to_id(&self) -> u64 {
        self.0
    }

    fn parse(input: &str) -> IResult<&str, &str> {
        let (input, _) = tag("r")(input)?;
        let (input, value) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)?;
        Ok((input, value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_new() {
        assert_eq!(1, Register::new("r1").unwrap().to_id());
        assert_eq!(12, Register::new("r12").unwrap().to_id());
        assert_eq!(123, Register::new("r123").unwrap().to_id());
        assert_eq!(1234, Register::new("r1_234").unwrap().to_id());
        assert_eq!(12345, Register::new("r12_345").unwrap().to_id());
        assert_eq!(123456, Register::new("r123_456").unwrap().to_id());
        assert_eq!(1234567, Register::new("r1_2_3_4_5_6_7").unwrap().to_id());
        assert_eq!(1234567, Register::new("r1_2_3_4_5_67_").unwrap().to_id());
    }

    #[test]
    fn test_malformed_register() {
        assert!(Register::new("r_123").is_err());
        assert!(Register::new("r123_").is_err());
        assert!(Register::new("5u_8").is_err());
    }
}
