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

use crate::ir;

use anyhow::*;

pub enum GroupCoordinate {
    Field(Vec<u64>),
    SignHigh,
    SignLow,
    Inferred,
}

impl GroupCoordinate {
    pub(crate) fn decode(from: ir::GroupCoordinate) -> Result<GroupCoordinate> {
        match from.coordinate_type {
            x if x == ir::GroupCoordinateType::Field as i32 => Ok(GroupCoordinate::Field(from.value)),
            x if x == ir::GroupCoordinateType::SignHigh as i32 => Ok(GroupCoordinate::SignHigh),
            x if x == ir::GroupCoordinateType::SignLow as i32 => Ok(GroupCoordinate::SignLow),
            x if x == ir::GroupCoordinateType::Inferred as i32 => Ok(GroupCoordinate::Inferred),
            x => Err(anyhow!("unknown group coordinate type: {}", x)),
        }
    }

    pub(crate) fn encode(&self) -> ir::GroupCoordinate {
        ir::GroupCoordinate {
            coordinate_type: match self {
                GroupCoordinate::Field(_) => ir::GroupCoordinateType::Field as i32,
                GroupCoordinate::SignHigh => ir::GroupCoordinateType::SignHigh as i32,
                GroupCoordinate::SignLow => ir::GroupCoordinateType::SignLow as i32,
                GroupCoordinate::Inferred => ir::GroupCoordinateType::Inferred as i32,
            },
            value: match self {
                GroupCoordinate::Field(f) => f.clone(),
                _ => vec![],
            },
        }
    }
}

pub enum Integer {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),

    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
}

/// A constant value in IR representation or variable reference
pub enum Value {
    Address(Vec<u8>),
    Boolean(bool),
    Char(u32),
    Field(Vec<u64>),
    Group(GroupCoordinate, Option<GroupCoordinate>),
    Integer(Integer),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Ref(u32), // reference to a variable
}

impl Value {
    pub(crate) fn decode(from: ir::Operand) -> Result<Value> {
        Ok(match from {
            ir::Operand {
                address: Some(address), ..
            } if !address.address.is_empty() => Value::Address(address.address),
            ir::Operand {
                boolean: Some(boolean), ..
            } => Value::Boolean(boolean.boolean),
            ir::Operand { char: Some(char), .. } => Value::Char(char.char),
            ir::Operand { field, .. } if !field.is_empty() => Value::Field(field),
            ir::Operand { group_single, .. } if !group_single.is_empty() => {
                Value::Group(GroupCoordinate::Field(group_single), None)
            }
            ir::Operand {
                group_tuple:
                    Some(ir::Group {
                        left: Some(left),
                        right: Some(right),
                    }),
                ..
            } => Value::Group(GroupCoordinate::decode(left)?, Some(GroupCoordinate::decode(right)?)),
            ir::Operand { u8: Some(u8), .. } => Value::Integer(Integer::U8(u8.u8 as u8)),
            ir::Operand { u16: Some(u16), .. } => Value::Integer(Integer::U16(u16.u16 as u16)),
            ir::Operand { u32: Some(u32), .. } => Value::Integer(Integer::U32(u32.u32)),
            ir::Operand { u64: Some(u64), .. } => Value::Integer(Integer::U64(u64.u64)),
            ir::Operand { u128: Some(u128), .. } => {
                let mut raw = [0u8; 16];
                let len = u128.u128.len().min(16);
                (&mut raw[..len]).copy_from_slice(&u128.u128[..len]);
                Value::Integer(Integer::U128(u128::from_le_bytes(raw)))
            }
            ir::Operand { i8: Some(i8), .. } => Value::Integer(Integer::I8(i8.i8 as i8)),
            ir::Operand { i16: Some(i16), .. } => Value::Integer(Integer::I16(i16.i16 as i16)),
            ir::Operand { i32: Some(i32), .. } => Value::Integer(Integer::I32(i32.i32)),
            ir::Operand { i64: Some(i64), .. } => Value::Integer(Integer::I64(i64.i64)),
            ir::Operand { i128: Some(i128), .. } => {
                let mut raw = [0u8; 16];
                let len = i128.i128.len().min(16);
                (&mut raw[..len]).copy_from_slice(&i128.i128[..len]);
                Value::Integer(Integer::I128(i128::from_le_bytes(raw)))
            }
            ir::Operand { array: Some(array), .. } => Value::Array(
                array
                    .array
                    .into_iter()
                    .map(|x| Value::decode(x))
                    .collect::<Result<Vec<_>>>()?,
            ),
            ir::Operand { tuple: Some(tuple), .. } => Value::Tuple(
                tuple
                    .tuple
                    .into_iter()
                    .map(|x| Value::decode(x))
                    .collect::<Result<Vec<_>>>()?,
            ),
            ir::Operand {
                variable_ref: Some(variable_ref),
                ..
            } => Value::Ref(variable_ref.variable_ref),
            _ => return Err(anyhow!("illegal operand state")),
        })
    }

    pub(crate) fn encode(&self) -> ir::Operand {
        match self {
            Value::Address(address) => ir::Operand {
                address: Some(ir::Address {
                    address: address.clone(),
                }),
                ..Default::default()
            },
            Value::Boolean(value) => ir::Operand {
                boolean: Some(ir::Bool { boolean: *value }),
                ..Default::default()
            },
            Value::Char(c) => ir::Operand {
                char: Some(ir::Char { char: *c }),
                ..Default::default()
            },
            Value::Field(field) => ir::Operand {
                field: field.clone(),
                ..Default::default()
            },
            Value::Group(GroupCoordinate::Field(inner), None) => ir::Operand {
                group_single: inner.clone(),
                ..Default::default()
            },
            Value::Group(_, None) => unimplemented!("cannot have unit group with inference"),
            Value::Group(left, Some(right)) => ir::Operand {
                group_tuple: Some(ir::Group {
                    left: Some(left.encode()),
                    right: Some(right.encode()),
                }),
                ..Default::default()
            },
            Value::Integer(i) => match i {
                Integer::U8(i) => ir::Operand {
                    u8: Some(ir::U8 { u8: *i as u32 }),
                    ..Default::default()
                },
                Integer::U16(i) => ir::Operand {
                    u16: Some(ir::U16 { u16: *i as u32 }),
                    ..Default::default()
                },
                Integer::U32(i) => ir::Operand {
                    u32: Some(ir::U32 { u32: *i }),
                    ..Default::default()
                },
                Integer::U64(i) => ir::Operand {
                    u64: Some(ir::U64 { u64: *i }),
                    ..Default::default()
                },
                Integer::U128(i) => ir::Operand {
                    u128: Some(ir::U128 {
                        u128: i.to_le_bytes().to_vec(),
                    }),
                    ..Default::default()
                },
                Integer::I8(i) => ir::Operand {
                    i8: Some(ir::I8 { i8: *i as i32 }),
                    ..Default::default()
                },
                Integer::I16(i) => ir::Operand {
                    i16: Some(ir::I16 { i16: *i as i32 }),
                    ..Default::default()
                },
                Integer::I32(i) => ir::Operand {
                    i32: Some(ir::I32 { i32: *i }),
                    ..Default::default()
                },
                Integer::I64(i) => ir::Operand {
                    i64: Some(ir::I64 { i64: *i as i64 }),
                    ..Default::default()
                },
                Integer::I128(i) => ir::Operand {
                    i128: Some(ir::I128 {
                        i128: i.to_le_bytes().to_vec(),
                    }),
                    ..Default::default()
                },
            },
            Value::Array(items) => ir::Operand {
                array: Some(ir::Array {
                    array: items.iter().map(|x| x.encode()).collect(),
                }),
                ..Default::default()
            },
            Value::Tuple(items) => ir::Operand {
                tuple: Some(ir::Tuple {
                    tuple: items.iter().map(|x| x.encode()).collect(),
                }),
                ..Default::default()
            },
            Value::Ref(variable_ref) => ir::Operand {
                variable_ref: Some(ir::VariableRef {
                    variable_ref: *variable_ref,
                }),
                ..Default::default()
            },
        }
    }
}
