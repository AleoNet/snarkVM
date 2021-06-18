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

use crate::{ir, Value};

use anyhow::*;
use num_enum::TryFromPrimitive;

use super::{decode_control_string, decode_control_u32};

#[derive(Clone, Debug)]
pub struct MaskData {
    pub instruction_count: u32,
    pub condition: Value,
}

impl MaskData {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() != 2 {
            return Err(anyhow!("illegal operand count for MaskData: {}", operands.len()));
        }
        let mut operands = operands.into_iter();
        let instruction_count = decode_control_u32(operands.next().unwrap())?;
        let condition = Value::decode(operands.next().unwrap())?;
        Ok(Self {
            instruction_count,
            condition,
        })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        let mut operands = vec![];
        operands.push(ir::Operand {
            u32: Some(ir::U32 {
                u32: self.instruction_count,
            }),
            ..Default::default()
        });
        operands.push(self.condition.encode());
        operands
    }
}

#[derive(Clone, Debug)]
pub struct RepeatData {
    pub instruction_count: u32,
    pub iter_variable: u32,
    pub from: Value,
    pub to: Value,
}

impl RepeatData {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() != 3 {
            return Err(anyhow!("illegal operand count for RepeatData: {}", operands.len()));
        }
        let mut operands = operands.into_iter();
        let instruction_count = decode_control_u32(operands.next().unwrap())?;
        let iter_variable = decode_control_u32(operands.next().unwrap())?;
        let from = Value::decode(operands.next().unwrap())?;
        let to = Value::decode(operands.next().unwrap())?;
        Ok(Self {
            instruction_count,
            iter_variable,
            from,
            to,
        })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        let mut operands = vec![];
        operands.push(ir::Operand {
            u32: Some(ir::U32 {
                u32: self.instruction_count,
            }),
            ..Default::default()
        });
        operands.push(ir::Operand {
            u32: Some(ir::U32 {
                u32: self.iter_variable,
            }),
            ..Default::default()
        });
        operands.push(self.from.encode());
        operands.push(self.to.encode());
        operands
    }
}

#[derive(Clone, Debug)]
pub struct CallData {
    pub destination: u32,
    pub index: u32, // index of function (of all defined functions, not instruction index)
    pub arguments: Vec<Value>,
}

impl CallData {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() < 2 {
            return Err(anyhow!("illegal operand count for RepeatData: {}", operands.len()));
        }
        let mut operands = operands.into_iter();
        let destination = decode_control_u32(operands.next().unwrap())?;
        let index = decode_control_u32(operands.next().unwrap())?;
        let arguments = operands.map(Value::decode).collect::<Result<Vec<Value>>>()?;
        Ok(Self {
            destination,
            index,
            arguments,
        })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        let mut operands = vec![];
        operands.push(ir::Operand {
            u32: Some(ir::U32 { u32: self.destination }),
            ..Default::default()
        });
        operands.push(ir::Operand {
            u32: Some(ir::U32 { u32: self.index }),
            ..Default::default()
        });
        for value in self.arguments.iter() {
            operands.push(value.encode());
        }
        operands
    }
}

#[derive(Clone, Debug)]
pub struct CallCoreData {
    pub destination: u32,
    pub identifier: String, // name of core function
    pub arguments: Vec<Value>,
}

impl CallCoreData {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() < 2 {
            return Err(anyhow!("illegal operand count for RepeatData: {}", operands.len()));
        }
        let mut operands = operands.into_iter();
        let destination = decode_control_u32(operands.next().unwrap())?;
        let identifier = decode_control_string(operands.next().unwrap())?;
        let arguments = operands.map(Value::decode).collect::<Result<Vec<Value>>>()?;
        Ok(Self {
            destination,
            identifier,
            arguments,
        })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        let mut operands = vec![];
        operands.push(ir::Operand {
            u32: Some(ir::U32 { u32: self.destination }),
            ..Default::default()
        });
        operands.push(ir::Operand {
            string: Some(ir::String {
                string: self.identifier.clone(),
            }),
            ..Default::default()
        });
        for value in self.arguments.iter() {
            operands.push(value.encode());
        }
        operands
    }
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, TryFromPrimitive)]
pub enum LogLevel {
    Error = 0,
    Info,
    Debug,
}

#[derive(Clone, Debug)]
pub struct LogData {
    pub log_level: LogLevel,
    pub parts: Vec<Value>,
}

impl LogData {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() < 2 {
            return Err(anyhow!("illegal operand count for RepeatData: {}", operands.len()));
        }
        let mut operands = operands.into_iter();
        let log_level = LogLevel::try_from_primitive(decode_control_u32(operands.next().unwrap())?)?;
        let parts = operands.map(Value::decode).collect::<Result<Vec<Value>>>()?;
        Ok(Self { log_level, parts })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        let mut operands = vec![];
        operands.push(ir::Operand {
            u32: Some(ir::U32 {
                u32: self.log_level as u32,
            }),
            ..Default::default()
        });
        for value in self.parts.iter() {
            operands.push(value.encode());
        }
        operands
    }
}

#[derive(Clone, Debug)]
pub struct PredicateData<const N: usize> {
    pub values: Vec<Value>,
}

impl<const N: usize> PredicateData<N> {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() != N {
            return Err(anyhow!("illegal operand count for PredicateData: {}", operands.len()));
        }
        Ok(Self {
            values: operands
                .into_iter()
                .map(Value::decode)
                .collect::<Result<Vec<Value>>>()?,
        })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        self.values.iter().map(|x| x.encode()).collect()
    }
}
