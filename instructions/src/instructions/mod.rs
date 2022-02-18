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

pub enum Instruction<E: Environment, I: IntegerType> {
    Add(Add),
    AddChecked(AddChecked),
    AddWrapped(AddWrapped),
    And(And),
    Eq(Eq),
    LoadBaseField(LoadBaseField<E>),
    LoadBoolean(LoadBoolean<E>),
    LoadGroup(LoadGroup<E>),
    LoadInteger(LoadInteger<E, I>),
    LoadScalarField(LoadScalarField<E>),
    Sub(Sub),
    SubChecked(SubChecked),
    SubWrapped(SubWrapped),
    Ter(Ter),
}

impl<E: Environment, I: IntegerType> Instruction<E, I> {
    pub fn new(input: &str) -> ParserResult<Self> {
        let mut parse_instruction = alt((
            Self::parse_add_instruction,
            Self::parse_add_checked_instruction,
            Self::parse_add_wrapped_instruction,
            Self::parse_and_instruction,
            Self::parse_eq_instruction,
            Self::parse_load_base_field_instruction,
            Self::parse_load_boolean_instruction,
            Self::parse_load_group_instruction,
            Self::parse_load_integer_instruction,
            Self::parse_load_scalar_field_instruction,
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

    fn parse_load_integer_instruction(input: &str) -> ParserResult<Self> {
        let (input, instruction) = LoadInteger::new(input)?;
        Ok((input, Self::LoadInteger(instruction)))
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
