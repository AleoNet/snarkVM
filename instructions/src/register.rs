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
    index: u64,
    typ: Type,
}

impl Register {
    pub fn new(input: &str) -> ParserResult<Self> {
        let parse_zero = recognize(tag("0"));
        let parse_nonzero = recognize(pair(one_of("123456789"), many0(one_of("0123456789"))));

        let (input, _) = tag("r")(input)?;
        let (input, index) = map_res(alt((parse_zero, parse_nonzero)), |v| String::from(v).parse::<u64>())(input)?;
        let (input, _) = tag(".")(input)?;
        let (input, typ) = Type::new(input)?;
        Ok((input, Self { index, typ }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_new() {
        // TODO (@pranav)
        //  This is just a sanity check. Need to construct a comprehensive test framework.
        assert_eq!(1, TypedRegister::new("bf.r1").unwrap().1.unwrap().get_id());
        assert_eq!(12, TypedRegister::new("b.r12").unwrap().1.unwrap().get_id());
        assert_eq!(123, TypedRegister::new("g.r123").unwrap().1.unwrap().get_id());
        assert_eq!(1234, TypedRegister::new("i8.r1_234").unwrap().1.unwrap().get_id());
        assert_eq!(12345, TypedRegister::new("i16.r12_345").unwrap().1.unwrap().get_id());
        assert_eq!(123456, TypedRegister::new("i32.r123_456").unwrap().1.unwrap().get_id());
        assert_eq!(1234567, TypedRegister::new("i64.r1_2_3_4_5_6_7").unwrap().1.unwrap().get_id());
        assert_eq!(1, TypedRegister::new("i128.r1").unwrap().1.unwrap().get_id());
        assert_eq!(12, TypedRegister::new("sf.r12").unwrap().1.unwrap().get_id());
        assert_eq!(123, TypedRegister::new("u8.r123").unwrap().1.unwrap().get_id());
        assert_eq!(1234, TypedRegister::new("u16.r1_234").unwrap().1.unwrap().get_id());
        assert_eq!(12345, TypedRegister::new("u32.r12_345").unwrap().1.unwrap().get_id());
        assert_eq!(123456, TypedRegister::new("u64.r123_456").unwrap().1.unwrap().get_id());
        assert_eq!(1234567, TypedRegister::new("u128.r1_2_3_4_5_6_7").unwrap().1.unwrap().get_id());
    }

    #[test]
    fn test_malformed_register() {
        // TODO: Check that you cannot have leading zeros for register numbers.
        assert!(TypedRegister::new("r_123").is_err());
        // assert!(TypedRegister::new("r123_").is_err());
        assert!(TypedRegister::new("5u_8").is_err());
    }
}
