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

pub mod add;
pub use add::*;

pub mod add_checked;
pub use add_checked::*;

pub mod add_wrapped;
pub use add_wrapped::*;

pub mod and;
pub use and::*;

pub mod eq;
pub use eq::*;

pub mod load_immediate;
pub use load_immediate::*;

pub mod sub;
pub use sub::*;

pub mod sub_checked;
pub use sub_checked::*;

pub mod sub_wrapped;
pub use sub_wrapped::*;

pub mod ter;
pub use ter::*;

use crate::ParserResult;
use nom::branch::alt;
use snarkvm_circuits::{Environment, IntegerType};

pub enum Instruction<E: Environment> {
    Add(Add),
    AddChecked(AddChecked),
    AddWrapped(AddWrapped),
    And(And),
    Eq(Eq),
    LoadBaseField(LoadBaseField<E>),
    LoadBoolean(LoadBoolean<E>),
    LoadGroup(LoadGroup<E>),
    LoadU8(LoadU8<E>),
    LoadU16(LoadU16<E>),
    LoadU32(LoadU32<E>),
    LoadU64(LoadU64<E>),
    LoadU128(LoadU128<E>),
    LoadI8(LoadI8<E>),
    LoadI16(LoadI16<E>),
    LoadI32(LoadI32<E>),
    LoadI64(LoadI64<E>),
    LoadI128(LoadI128<E>),
    LoadScalarField(LoadScalarField<E>),
    Sub(Sub),
    SubChecked(SubChecked),
    SubWrapped(SubWrapped),
    Ter(Ter),
}

impl<E: Environment> Instruction<E> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let mut parse_load = alt((
            Self::parse_load_base_field_instruction,
            Self::parse_load_boolean_instruction,
            Self::parse_load_group_instruction,
            Self::parse_load_u8_instruction,
            Self::parse_load_u16_instruction,
            Self::parse_load_u32_instruction,
            Self::parse_load_u64_instruction,
            Self::parse_load_u128_instruction,
            Self::parse_load_i8_instruction,
            Self::parse_load_i16_instruction,
            Self::parse_load_i32_instruction,
            Self::parse_load_i64_instruction,
            Self::parse_load_i128_instruction,
            Self::parse_load_scalar_field_instruction,
        ));
        let mut parse_instruction = alt((
            parse_load,
            Self::parse_add_instruction,
            Self::parse_add_checked_instruction,
            Self::parse_add_wrapped_instruction,
            Self::parse_and_instruction,
            Self::parse_eq_instruction,
            Self::parse_sub_instruction,
            Self::parse_sub_checked_instruction,
            Self::parse_sub_wrapped_instruction,
            Self::parse_ter_instruction,
        ));
        parse_instruction(input)
    }

    fn parse_add_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = Add::new(input)?;
        Ok((input, Self::Add(instruction)))
    }

    fn parse_add_checked_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = AddChecked::new(input)?;
        Ok((input, Self::AddChecked(instruction)))
    }

    fn parse_add_wrapped_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = AddWrapped::new(input)?;
        Ok((input, Self::AddWrapped(instruction)))
    }

    fn parse_and_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = And::new(input)?;
        Ok((input, Self::And(instruction)))
    }

    fn parse_eq_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = Eq::new(input)?;
        Ok((input, Self::Eq(instruction)))
    }

    fn parse_load_base_field_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadBaseField::new(input)?;
        Ok((input, Self::LoadBaseField(instruction)))
    }

    fn parse_load_boolean_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadBoolean::new(input)?;
        Ok((input, Self::LoadBoolean(instruction)))
    }

    fn parse_load_group_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadGroup::new(input)?;
        Ok((input, Self::LoadGroup(instruction)))
    }

    fn parse_load_u8_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadU8::<E>::new(input)?;
        Ok((input, Self::LoadU8(instruction)))
    }

    fn parse_load_u16_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadU16::<E>::new(input)?;
        Ok((input, Self::LoadU16(instruction)))
    }

    fn parse_load_u32_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadU32::<E>::new(input)?;
        Ok((input, Self::LoadU32(instruction)))
    }

    fn parse_load_u64_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadU64::<E>::new(input)?;
        Ok((input, Self::LoadU64(instruction)))
    }

    fn parse_load_u128_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadU128::<E>::new(input)?;
        Ok((input, Self::LoadU128(instruction)))
    }

    fn parse_load_i8_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadI8::<E>::new(input)?;
        Ok((input, Self::LoadI8(instruction)))
    }

    fn parse_load_i16_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadI16::<E>::new(input)?;
        Ok((input, Self::LoadI16(instruction)))
    }

    fn parse_load_i32_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadI32::<E>::new(input)?;
        Ok((input, Self::LoadI32(instruction)))
    }

    fn parse_load_i64_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadI64::<E>::new(input)?;
        Ok((input, Self::LoadI64(instruction)))
    }

    fn parse_load_i128_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadI128::<E>::new(input)?;
        Ok((input, Self::LoadI128(instruction)))
    }

    fn parse_load_scalar_field_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadScalarField::new(input)?;
        Ok((input, Self::LoadScalarField(instruction)))
    }

    fn parse_sub_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = Sub::new(input)?;
        Ok((input, Self::Sub(instruction)))
    }

    fn parse_sub_checked_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = SubChecked::new(input)?;
        Ok((input, Self::SubChecked(instruction)))
    }

    fn parse_sub_wrapped_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = SubWrapped::new(input)?;
        Ok((input, Self::SubWrapped(instruction)))
    }

    fn parse_ter_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = Ter::new(input)?;
        Ok((input, Self::Ter(instruction)))
    }
}

#[cfg(test)]
mod test {
    use crate::Instruction;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_instruction_new() {
        type E = Circuit;
        let (input, instruction) = Instruction::<E>::new("addc u8.r3, u8.r2, u8.r1;").unwrap();
        assert_eq!(input, "");
    }
}
