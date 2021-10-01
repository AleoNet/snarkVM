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

use crate::{Address, Char, FieldType, GroupType, Integer};

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    bits::Boolean,
    integers::uint::UInt8,
    traits::{eq::ConditionalEqGadget, select::CondSelectGadget},
};
use snarkvm_ir::Type;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use std::fmt;

use anyhow::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstrainedValue<F: PrimeField, G: GroupType<F>> {
    // Data types
    Address(Address),
    Boolean(Boolean),
    Char(Char<F>),
    Field(FieldType<F>),
    Group(G),
    Integer(Integer),

    // Arrays
    Array(Vec<ConstrainedValue<F, G>>),

    // Tuples
    Tuple(Vec<ConstrainedValue<F, G>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleInt {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl fmt::Display for SimpleInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SimpleInt::*;

        match self {
            I8 => write!(f, "i8"),
            I16 => write!(f, "i16"),
            I32 => write!(f, "i32"),
            I64 => write!(f, "i64"),
            I128 => write!(f, "i128"),
            U8 => write!(f, "u8"),
            U16 => write!(f, "u16"),
            U32 => write!(f, "u32"),
            U64 => write!(f, "u64"),
            U128 => write!(f, "u128"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleType {
    // Data types
    Address,
    Boolean,
    Char,
    Field,
    Group,
    Integer(SimpleInt),

    // Arrays
    Array(Box<SimpleType>, usize),

    // Tuples
    Tuple(Vec<SimpleType>),
}

impl fmt::Display for SimpleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SimpleType::*;

        match self {
            Address => write!(f, "address"),
            Boolean => write!(f, "bool"),
            Char => write!(f, "char"),
            Field => write!(f, "field"),
            Group => write!(f, "group"),
            Integer(int) => write!(f, "{}", int),
            Array(inner, size) => write!(f, "[{}; {}]", inner, size),
            Tuple(values) => {
                write!(f, "(")?;
                write!(
                    f,
                    "{}",
                    values.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(",")
                )?;
                write!(f, ")")
            }
        }
    }
}

impl<F: PrimeField, G: GroupType<F>> ConstrainedValue<F, G> {
    pub fn extract_bool(&self) -> Result<&Boolean, &Self> {
        match self {
            ConstrainedValue::Boolean(x) => Ok(x),
            value => Err(value),
        }
    }

    pub fn extract_integer(&self) -> Result<&Integer, &Self> {
        match self {
            ConstrainedValue::Integer(x) => Ok(x),
            value => Err(value),
        }
    }

    pub fn extract_array(&self) -> Result<&Vec<Self>, &Self> {
        match self {
            ConstrainedValue::Array(x) => Ok(x),
            value => Err(value),
        }
    }

    pub fn extract_tuple(&self) -> Result<&Vec<Self>, &Self> {
        match self {
            ConstrainedValue::Tuple(x) => Ok(x),
            value => Err(value),
        }
    }

    pub fn matches_input_type(&self, type_: &Type) -> bool {
        match (self, type_) {
            (ConstrainedValue::Address(_), Type::Address)
            | (ConstrainedValue::Boolean(_), Type::Boolean)
            | (ConstrainedValue::Field(_), Type::Field)
            | (ConstrainedValue::Char(_), Type::Char)
            | (ConstrainedValue::Group(_), Type::Group)
            | (ConstrainedValue::Integer(Integer::I8(_)), Type::I8)
            | (ConstrainedValue::Integer(Integer::I16(_)), Type::I16)
            | (ConstrainedValue::Integer(Integer::I32(_)), Type::I32)
            | (ConstrainedValue::Integer(Integer::I64(_)), Type::I64)
            | (ConstrainedValue::Integer(Integer::I128(_)), Type::I128)
            | (ConstrainedValue::Integer(Integer::U8(_)), Type::U8)
            | (ConstrainedValue::Integer(Integer::U16(_)), Type::U16)
            | (ConstrainedValue::Integer(Integer::U32(_)), Type::U32)
            | (ConstrainedValue::Integer(Integer::U64(_)), Type::U64)
            | (ConstrainedValue::Integer(Integer::U128(_)), Type::U128) => true,
            (ConstrainedValue::Array(inner), Type::Array(inner_type, len)) => {
                let len_match = match len {
                    Some(l) => inner.len() == *l as usize,
                    None => true,
                };
                len_match && inner.iter().all(|inner| inner.matches_input_type(&**inner_type))
            }
            (ConstrainedValue::Tuple(values), Type::Tuple(types)) => values
                .iter()
                .zip(types.iter())
                .all(|(value, type_)| value.matches_input_type(type_)),
            (ConstrainedValue::Tuple(values), Type::Circuit(members)) => values
                .iter()
                .zip(members.iter())
                .all(|(value, (_, type_))| value.matches_input_type(type_)),
            (_, _) => false,
        }
    }

    pub fn to_bits_le(&self) -> Result<Vec<Boolean>> {
        use ConstrainedValue::*;

        match self {
            Address(_) => Err(anyhow!("the type `address` does not implement the to_bits_le method")),
            Boolean(_) => Err(anyhow!("the type `bool` does not implement the to_bits_le method")),
            Char(_) => Err(anyhow!("the type `char` does not implement the to_bits_le method")),
            Field(_) => Err(anyhow!("the type `field` does not implement the to_bits_le method")),
            Group(_) => Err(anyhow!("the type `group` does not implement the to_bits_le method")),
            Integer(integer) => Ok(integer.to_bits_le()),
            Array(_) => Err(anyhow!("the type `array` does not implement the to_bits_le method")),
            Tuple(_) => Err(anyhow!("the type `tuple` does not implement the to_bits_le method")),
        }
    }

    pub fn from_bits_le(type_: SimpleType, bits: &[Boolean]) -> Result<Self> {
        use snarkvm_gadgets::{
            integers::{int::*, uint::*},
            Integer as IntegerTrait,
        };

        match type_ {
            SimpleType::Integer(SimpleInt::I8) => Ok(Self::Integer(Integer::I8(Int8::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::I16) => Ok(Self::Integer(Integer::I16(Int16::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::I32) => Ok(Self::Integer(Integer::I32(Int32::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::I64) => Ok(Self::Integer(Integer::I64(Int64::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::I128) => Ok(Self::Integer(Integer::I128(Int128::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::U8) => Ok(Self::Integer(Integer::U8(UInt8::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::U16) => Ok(Self::Integer(Integer::U16(UInt16::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::U32) => Ok(Self::Integer(Integer::U32(UInt32::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::U64) => Ok(Self::Integer(Integer::U64(UInt64::from_bits_le(bits)))),
            SimpleType::Integer(SimpleInt::U128) => Ok(Self::Integer(Integer::U128(UInt128::from_bits_le(bits)))),
            _ => Err(anyhow!(
                "the type `{}` does not implement the from_bits_le method",
                type_
            )),
        }
    }

    pub fn to_bytes_le(&self) -> Result<Vec<UInt8>> {
        use ConstrainedValue::*;

        match self {
            Address(_) => Err(anyhow!("the type `address` does not implement the to_bytes_le method")),
            Boolean(_) => Err(anyhow!("the type `bool` does not implement the to_bytes_le method")),
            Char(_) => Err(anyhow!("the type `char` does not implement the to_bytes_le method")),
            Field(_) => Err(anyhow!("the type `field` does not implement the to_bytes_le method")),
            Group(_) => Err(anyhow!("the type `group` does not implement the to_bytes_le method")),
            Integer(_) => Err(anyhow!("the type `int` does not implement the to_bytes_le method")),
            Array(_) => Err(anyhow!("the type `array` does not implement the to_bytes_le method")),
            Tuple(_) => Err(anyhow!("the type `tuple` does not implement the to_bytes_le method")),
        }
    }

    pub fn from_bytes_le(type_: SimpleType, _bytes: &[UInt8]) -> Result<Self> {
        Err(anyhow!(
            "the type `{}` does not implement the from_bytes_le method",
            type_
        ))
    }
}

impl<F: PrimeField, G: GroupType<F>> fmt::Display for ConstrainedValue<F, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            // Data types
            ConstrainedValue::Address(ref value) => write!(f, "{}", value),
            ConstrainedValue::Boolean(ref value) => write!(
                f,
                "{}",
                value
                    .get_value()
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "[allocated]".to_string())
            ),
            ConstrainedValue::Char(ref value) => write!(f, "{}", value),
            ConstrainedValue::Field(ref value) => write!(f, "{:?}", value),
            ConstrainedValue::Group(ref value) => write!(f, "{:?}", value),
            ConstrainedValue::Integer(ref value) => write!(f, "{}", value),

            // Data type wrappers
            ConstrainedValue::Array(ref array) => {
                if matches!(array[0], ConstrainedValue::Char(_)) {
                    for character in array {
                        write!(f, "{}", character)?;
                    }

                    Ok(())
                } else {
                    write!(f, "[")?;
                    for (i, e) in array.iter().enumerate() {
                        write!(f, "{}", e)?;
                        if i < array.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, "]")
                }
            }
            ConstrainedValue::Tuple(ref tuple) => {
                let values = tuple.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ");

                write!(f, "({})", values)
            }
        }
    }
}

impl<F: PrimeField, G: GroupType<F>> ConditionalEqGadget<F> for ConstrainedValue<F, G> {
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        match (self, other) {
            (ConstrainedValue::Address(address_1), ConstrainedValue::Address(address_2)) => {
                address_1.conditional_enforce_equal(cs, address_2, condition)
            }
            (ConstrainedValue::Boolean(bool_1), ConstrainedValue::Boolean(bool_2)) => {
                bool_1.conditional_enforce_equal(cs, bool_2, condition)
            }
            (ConstrainedValue::Char(char_1), ConstrainedValue::Char(char_2)) => {
                char_1.conditional_enforce_equal(cs, char_2, condition)
            }
            (ConstrainedValue::Field(field_1), ConstrainedValue::Field(field_2)) => {
                field_1.conditional_enforce_equal(cs, field_2, condition)
            }
            (ConstrainedValue::Group(group_1), ConstrainedValue::Group(group_2)) => {
                group_1.conditional_enforce_equal(cs, group_2, condition)
            }
            (ConstrainedValue::Integer(num_1), ConstrainedValue::Integer(num_2)) => {
                num_1.conditional_enforce_equal(cs, num_2, condition)
            }
            (ConstrainedValue::Array(arr_1), ConstrainedValue::Array(arr_2)) => {
                if arr_1.len() != arr_2.len() {
                    return Err(SynthesisError::Unsatisfiable);
                }

                for (i, (left, right)) in arr_1.iter().zip(arr_2.iter()).enumerate() {
                    left.conditional_enforce_equal(cs.ns(|| format!("array[{}]", i)), right, condition)?;
                }
                Ok(())
            }
            (ConstrainedValue::Tuple(tuple_1), ConstrainedValue::Tuple(tuple_2)) => {
                if tuple_1.len() != tuple_2.len() {
                    return Err(SynthesisError::Unsatisfiable);
                }

                for (i, (left, right)) in tuple_1.iter().zip(tuple_2.iter()).enumerate() {
                    left.conditional_enforce_equal(cs.ns(|| format!("tuple index {}", i)), right, condition)?;
                }
                Ok(())
            }
            (_, _) => Err(SynthesisError::Unsatisfiable),
        }
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<F: PrimeField, G: GroupType<F>> CondSelectGadget<F> for ConstrainedValue<F, G> {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(match (first, second) {
            (ConstrainedValue::Address(address_1), ConstrainedValue::Address(address_2)) => {
                ConstrainedValue::Address(Address::conditionally_select(cs, cond, address_1, address_2)?)
            }
            (ConstrainedValue::Boolean(bool_1), ConstrainedValue::Boolean(bool_2)) => {
                ConstrainedValue::Boolean(Boolean::conditionally_select(cs, cond, bool_1, bool_2)?)
            }
            (ConstrainedValue::Char(char_1), ConstrainedValue::Char(char_2)) => {
                ConstrainedValue::Char(Char::conditionally_select(cs, cond, char_1, char_2)?)
            }
            (ConstrainedValue::Field(field_1), ConstrainedValue::Field(field_2)) => {
                ConstrainedValue::Field(FieldType::conditionally_select(cs, cond, field_1, field_2)?)
            }
            (ConstrainedValue::Group(group_1), ConstrainedValue::Group(group_2)) => {
                ConstrainedValue::Group(G::conditionally_select(cs, cond, group_1, group_2)?)
            }
            (ConstrainedValue::Integer(num_1), ConstrainedValue::Integer(num_2)) => {
                ConstrainedValue::Integer(Integer::conditionally_select(cs, cond, num_1, num_2)?)
            }
            (ConstrainedValue::Array(arr_1), ConstrainedValue::Array(arr_2)) => {
                if arr_1.len() != arr_2.len() {
                    return Err(SynthesisError::Unsatisfiable);
                }

                let mut array = Vec::with_capacity(arr_1.len());

                for (i, (first, second)) in arr_1.iter().zip(arr_2.iter()).enumerate() {
                    array.push(Self::conditionally_select(
                        cs.ns(|| format!("array[{}]", i)),
                        cond,
                        first,
                        second,
                    )?);
                }

                ConstrainedValue::Array(array)
            }
            (ConstrainedValue::Tuple(tuple_1), ConstrainedValue::Tuple(tuple_2)) => {
                if tuple_1.len() != tuple_2.len() {
                    return Err(SynthesisError::Unsatisfiable);
                }

                let mut array = Vec::with_capacity(tuple_1.len());

                for (i, (first, second)) in tuple_1.iter().zip(tuple_2.iter()).enumerate() {
                    array.push(Self::conditionally_select(
                        cs.ns(|| format!("tuple index {}", i)),
                        cond,
                        first,
                        second,
                    )?);
                }

                ConstrainedValue::Tuple(array)
            }
            (_, _) => return Err(SynthesisError::Unsatisfiable),
        })
    }

    fn cost() -> usize {
        unimplemented!() //lower bound 1, upper bound 128 or length of static array
    }
}
