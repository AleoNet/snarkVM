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

mod ndata;
pub use ndata::*;
mod array;
pub use array::*;
mod complex;
pub use complex::*;

mod op;
use num_enum::TryFromPrimitive;
use op::InstructionOp;

use anyhow::*;

use crate::ir;

#[derive(Clone, Debug)]
pub enum Instruction {
    // Binary
    Add(BinaryData),
    Sub(BinaryData),
    Mul(BinaryData),
    Div(BinaryData),
    Pow(BinaryData),
    Or(BinaryData),
    And(BinaryData),
    Eq(BinaryData),
    Ne(BinaryData),
    Ge(BinaryData),
    Gt(BinaryData),
    Le(BinaryData),
    Lt(BinaryData),
    BitOr(BinaryData),
    BitAnd(BinaryData),
    BitXor(BinaryData),
    Shr(BinaryData),
    ShrSigned(BinaryData),
    Shl(BinaryData),
    Mod(BinaryData),

    // Unary
    Not(UnaryData),
    Negate(UnaryData),
    BitNot(UnaryData),

    // Cast
    // Cast,

    // Arrays
    ArrayInitRepeat(ArrayInitRepeatData),
    ArrayInit(VarData),
    ArrayIndexGet(BinaryData),
    ArraySliceGet(QueryData<3>),
    ArrayIndexStore(QueryData<2>),
    ArraySliceStore(QueryData<3>),

    // Tuples
    TupleInit(VarData),
    TupleIndexGet(BinaryData),
    TupleIndexStore(QueryData<2>),

    // Complex Expressions
    Pick(QueryData<3>), // ternary / conditional move
    Mask(MaskData),     // mask side effects of following N instructions if condition is set
    Repeat(RepeatData), // const-count iteration of N following instructions with counter register at base

    // Variables
    Store(QueryData<1>),

    // Function Call
    Call(CallData),           // call a function
    Return(PredicateData<1>), // return from a function

    // Debugging
    Assert(PredicateData<1>),
    Log(LogData),

    // FFI/Core
    CallCore(CallCoreData),
}

impl Instruction {
    pub(crate) fn opcode(&self) -> InstructionOp {
        match self {
            Instruction::Add(_) => InstructionOp::Add,
            Instruction::Sub(_) => InstructionOp::Sub,
            Instruction::Mul(_) => InstructionOp::Mul,
            Instruction::Div(_) => InstructionOp::Div,
            Instruction::Pow(_) => InstructionOp::Pow,
            Instruction::Or(_) => InstructionOp::Or,
            Instruction::And(_) => InstructionOp::And,
            Instruction::Eq(_) => InstructionOp::Eq,
            Instruction::Ne(_) => InstructionOp::Ne,
            Instruction::Ge(_) => InstructionOp::Ge,
            Instruction::Gt(_) => InstructionOp::Gt,
            Instruction::Le(_) => InstructionOp::Le,
            Instruction::Lt(_) => InstructionOp::Lt,
            Instruction::BitOr(_) => InstructionOp::BitOr,
            Instruction::BitAnd(_) => InstructionOp::BitAnd,
            Instruction::BitXor(_) => InstructionOp::BitXor,
            Instruction::Shr(_) => InstructionOp::Shr,
            Instruction::ShrSigned(_) => InstructionOp::ShrSigned,
            Instruction::Shl(_) => InstructionOp::Shl,
            Instruction::Mod(_) => InstructionOp::Mod,
            Instruction::Not(_) => InstructionOp::Not,
            Instruction::Negate(_) => InstructionOp::Negate,
            Instruction::BitNot(_) => InstructionOp::BitNot,
            Instruction::ArrayInitRepeat(_) => InstructionOp::ArrayInitRepeat,
            Instruction::ArrayInit(_) => InstructionOp::ArrayInit,
            Instruction::ArrayIndexGet(_) => InstructionOp::ArrayIndexGet,
            Instruction::ArraySliceGet(_) => InstructionOp::ArraySliceGet,
            Instruction::ArrayIndexStore(_) => InstructionOp::ArrayIndexStore,
            Instruction::ArraySliceStore(_) => InstructionOp::ArraySliceStore,
            Instruction::TupleInit(_) => InstructionOp::TupleInit,
            Instruction::TupleIndexGet(_) => InstructionOp::TupleIndexGet,
            Instruction::TupleIndexStore(_) => InstructionOp::TupleIndexStore,
            Instruction::Pick(_) => InstructionOp::Pick,
            Instruction::Mask(_) => InstructionOp::Mask,
            Instruction::Repeat(_) => InstructionOp::Repeat,
            Instruction::Store(_) => InstructionOp::Store,
            Instruction::Call(_) => InstructionOp::Call,
            Instruction::Return(_) => InstructionOp::Return,
            Instruction::Assert(_) => InstructionOp::Assert,
            Instruction::Log(_) => InstructionOp::Log,
            Instruction::CallCore(_) => InstructionOp::CallCore,
        }
    }

    fn encode_operands(&self) -> Vec<ir::Operand> {
        match self {
            Instruction::Add(x) => x.encode(),
            Instruction::Sub(x) => x.encode(),
            Instruction::Mul(x) => x.encode(),
            Instruction::Div(x) => x.encode(),
            Instruction::Pow(x) => x.encode(),
            Instruction::Or(x) => x.encode(),
            Instruction::And(x) => x.encode(),
            Instruction::Eq(x) => x.encode(),
            Instruction::Ne(x) => x.encode(),
            Instruction::Ge(x) => x.encode(),
            Instruction::Gt(x) => x.encode(),
            Instruction::Le(x) => x.encode(),
            Instruction::Lt(x) => x.encode(),
            Instruction::BitOr(x) => x.encode(),
            Instruction::BitAnd(x) => x.encode(),
            Instruction::BitXor(x) => x.encode(),
            Instruction::Shr(x) => x.encode(),
            Instruction::ShrSigned(x) => x.encode(),
            Instruction::Shl(x) => x.encode(),
            Instruction::Mod(x) => x.encode(),
            Instruction::Not(x) => x.encode(),
            Instruction::Negate(x) => x.encode(),
            Instruction::BitNot(x) => x.encode(),
            Instruction::ArrayInitRepeat(x) => x.encode(),
            Instruction::ArrayInit(x) => x.encode(),
            Instruction::ArrayIndexGet(x) => x.encode(),
            Instruction::ArraySliceGet(x) => x.encode(),
            Instruction::ArrayIndexStore(x) => x.encode(),
            Instruction::ArraySliceStore(x) => x.encode(),
            Instruction::TupleInit(x) => x.encode(),
            Instruction::TupleIndexGet(x) => x.encode(),
            Instruction::TupleIndexStore(x) => x.encode(),
            Instruction::Pick(x) => x.encode(),
            Instruction::Mask(x) => x.encode(),
            Instruction::Repeat(x) => x.encode(),
            Instruction::Store(x) => x.encode(),
            Instruction::Call(x) => x.encode(),
            Instruction::Return(x) => x.encode(),
            Instruction::Assert(x) => x.encode(),
            Instruction::Log(x) => x.encode(),
            Instruction::CallCore(x) => x.encode(),
        }
    }

    pub(crate) fn encode(&self) -> ir::Instruction {
        ir::Instruction {
            opcode: self.opcode() as u32,
            operands: self.encode_operands(),
        }
    }

    pub(crate) fn decode(instruction: ir::Instruction) -> Result<Self> {
        Ok(
            match InstructionOp::try_from_primitive(instruction.opcode)
                .map_err(|_| anyhow!("unknown instruction opcode: {}", instruction.opcode))?
            {
                InstructionOp::Add => Instruction::Add(QueryData::decode(instruction.operands)?),
                InstructionOp::Sub => Instruction::Sub(QueryData::decode(instruction.operands)?),
                InstructionOp::Mul => Instruction::Mul(QueryData::decode(instruction.operands)?),
                InstructionOp::Div => Instruction::Div(QueryData::decode(instruction.operands)?),
                InstructionOp::Pow => Instruction::Pow(QueryData::decode(instruction.operands)?),
                InstructionOp::Or => Instruction::Or(QueryData::decode(instruction.operands)?),
                InstructionOp::And => Instruction::And(QueryData::decode(instruction.operands)?),
                InstructionOp::Eq => Instruction::Eq(QueryData::decode(instruction.operands)?),
                InstructionOp::Ne => Instruction::Ne(QueryData::decode(instruction.operands)?),
                InstructionOp::Ge => Instruction::Ge(QueryData::decode(instruction.operands)?),
                InstructionOp::Gt => Instruction::Gt(QueryData::decode(instruction.operands)?),
                InstructionOp::Le => Instruction::Le(QueryData::decode(instruction.operands)?),
                InstructionOp::Lt => Instruction::Lt(QueryData::decode(instruction.operands)?),
                InstructionOp::BitOr => Instruction::BitOr(QueryData::decode(instruction.operands)?),
                InstructionOp::BitAnd => Instruction::BitAnd(QueryData::decode(instruction.operands)?),
                InstructionOp::BitXor => Instruction::BitXor(QueryData::decode(instruction.operands)?),
                InstructionOp::Shr => Instruction::Shr(QueryData::decode(instruction.operands)?),
                InstructionOp::ShrSigned => Instruction::ShrSigned(QueryData::decode(instruction.operands)?),
                InstructionOp::Shl => Instruction::Shl(QueryData::decode(instruction.operands)?),
                InstructionOp::Mod => Instruction::Mod(QueryData::decode(instruction.operands)?),
                InstructionOp::Not => Instruction::Not(QueryData::decode(instruction.operands)?),
                InstructionOp::Negate => Instruction::Negate(QueryData::decode(instruction.operands)?),
                InstructionOp::BitNot => Instruction::BitNot(QueryData::decode(instruction.operands)?),
                InstructionOp::ArrayInitRepeat => {
                    Instruction::ArrayInitRepeat(ArrayInitRepeatData::decode(instruction.operands)?)
                }
                InstructionOp::ArrayInit => Instruction::ArrayInit(VarData::decode(instruction.operands)?),
                InstructionOp::ArrayIndexGet => Instruction::ArrayIndexGet(QueryData::decode(instruction.operands)?),
                InstructionOp::ArraySliceGet => Instruction::ArraySliceGet(QueryData::decode(instruction.operands)?),
                InstructionOp::ArrayIndexStore => {
                    Instruction::ArrayIndexStore(QueryData::decode(instruction.operands)?)
                }
                InstructionOp::ArraySliceStore => {
                    Instruction::ArraySliceStore(QueryData::decode(instruction.operands)?)
                }
                InstructionOp::TupleInit => Instruction::TupleInit(VarData::decode(instruction.operands)?),
                InstructionOp::TupleIndexGet => Instruction::TupleIndexGet(QueryData::decode(instruction.operands)?),
                InstructionOp::TupleIndexStore => {
                    Instruction::TupleIndexStore(QueryData::decode(instruction.operands)?)
                }
                InstructionOp::Pick => Instruction::Pick(QueryData::decode(instruction.operands)?),
                InstructionOp::Mask => Instruction::Mask(MaskData::decode(instruction.operands)?),
                InstructionOp::Repeat => Instruction::Repeat(RepeatData::decode(instruction.operands)?),
                InstructionOp::Store => Instruction::Store(QueryData::decode(instruction.operands)?),
                InstructionOp::Call => Instruction::Call(CallData::decode(instruction.operands)?),
                InstructionOp::Return => Instruction::Return(PredicateData::decode(instruction.operands)?),
                InstructionOp::Assert => Instruction::Assert(PredicateData::decode(instruction.operands)?),
                InstructionOp::Log => Instruction::Log(LogData::decode(instruction.operands)?),
                InstructionOp::CallCore => Instruction::CallCore(CallCoreData::decode(instruction.operands)?),
            },
        )
    }
}

fn decode_control_u32(operand: ir::Operand) -> Result<u32> {
    match operand {
        ir::Operand { u32: Some(u32), .. } => Ok(u32.u32),
        _ => Err(anyhow!("illegal value for control operand: {:?}", operand)),
    }
}

fn decode_control_string(operand: ir::Operand) -> Result<String> {
    match operand {
        ir::Operand {
            string: Some(string), ..
        } => Ok(string.string),
        _ => Err(anyhow!("illegal value for control operand: {:?}", operand)),
    }
}
