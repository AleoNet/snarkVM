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

use crate::{ParserResult, RegisterType};

use core::num::ParseIntError;
use nom::{
    bytes::complete::tag,
    character::complete::{char, one_of},
    combinator::recognize,
    multi::{many0, many1},
    sequence::terminated,
};

///
/// Typed registers have the syntactic form <RegisterType>.r<N>
///
// TODO (@pranav) Instead of a single typed register, consider having explicit
//  register structs for each of the types. This would result in stronger type
//  restrictions for instructions.
pub struct TypedRegister(RegisterType, u64);

impl TypedRegister {
    pub fn new(input: &str) -> ParserResult<Result<Self, ParseIntError>> {
        let (input, typ) = RegisterType::new(input)?;
        let (input, _) = tag(".r")(input)?;
        // TODO: (@pranav) Should remove underscores from register numbers.
        let (input, value) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(input)?;
        Ok((input, value.replace("_", "").parse::<u64>().and_then(|v| Ok(Self(typ?, v)))))
    }

    pub fn get_id(&self) -> u64 {
        self.1
    }

    pub fn get_type(&self) -> RegisterType {
        self.0
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
