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

use super::decode_control_u32;

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

pub struct RepeatData {
    pub instruction_count: u32,
    pub repeat_count: u32,
    pub base: Value,
}

impl RepeatData {
    pub(crate) fn decode(operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() != 3 {
            return Err(anyhow!("illegal operand count for RepeatData: {}", operands.len()));
        }
        let mut operands = operands.into_iter();
        let instruction_count = decode_control_u32(operands.next().unwrap())?;
        let repeat_count = decode_control_u32(operands.next().unwrap())?;
        let base = Value::decode(operands.next().unwrap())?;
        Ok(Self {
            instruction_count,
            repeat_count,
            base,
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
            u32: Some(ir::U32 { u32: self.repeat_count }),
            ..Default::default()
        });
        operands.push(self.base.encode());
        operands
    }
}

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
pub struct ReturnData {
    pub output: Value,
}

impl ReturnData {
    pub(crate) fn decode(mut operands: Vec<ir::Operand>) -> Result<Self> {
        if operands.len() != 1 {
            return Err(anyhow!("illegal operand count for ReturnData: {}", operands.len()));
        }
        Ok(Self {
            output: Value::decode(operands.remove(0))?,
        })
    }

    pub(crate) fn encode(&self) -> Vec<ir::Operand> {
        vec![self.output.encode()]
    }
}
