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

use crate::{ParserResult, Type};

use core::num::ParseIntError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::one_of,
    combinator::{map_res, recognize},
    multi::many0,
    sequence::pair,
};
use std::iter::FromIterator;

///
/// Typed registers have the syntactic form <RegisterType>.r<N>
///
// TODO (@pranav) Instead of a single typed register, consider having explicit
//  register structs for each of the types. This would result in stronger type
//  restrictions for instructions.
pub struct Register {
    pub(crate) typ: Type,
    pub(crate) id: u64,
}

impl Register {
    pub fn new(input: &str) -> ParserResult<Self> {
        let parse_zero = recognize(tag("0"));
        let parse_nonzero = recognize(pair(one_of("123456789"), many0(one_of("0123456789"))));

        let (input, typ) = Type::new(input)?;
        let (input, _) = tag(".")(input)?;
        let (input, _) = tag("r")(input)?;
        let (input, id) = map_res(alt((parse_zero, parse_nonzero)), |v| String::from(v).parse::<u64>())(input)?;

        Ok((input, Self { typ, id }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_new() {
        assert_eq!(0, Register::new("scalar.r0").unwrap().1.id);
        assert_eq!(1, Register::new("base.r1").unwrap().1.id);
        assert_eq!(12, Register::new("bool.r12").unwrap().1.id);
        assert_eq!(123, Register::new("group.r123").unwrap().1.id);
        assert_eq!(1234, Register::new("i8.r1234").unwrap().1.id);
        assert_eq!(12345, Register::new("i16.r12345").unwrap().1.id);
        assert_eq!(123456, Register::new("i32.r123456").unwrap().1.id);
        assert_eq!(1234567, Register::new("i64.r1234567").unwrap().1.id);
    }

    #[test]
    fn test_malformed_register() {
        assert!(Register::new("r_123").is_err());
        assert!(Register::new("r123_").is_err());
        assert!(Register::new("5u_8").is_err());
        assert!(Register::new("u8.r_123").is_err());
    }
}
