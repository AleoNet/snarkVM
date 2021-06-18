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

use num_enum::TryFromPrimitive;

#[derive(TryFromPrimitive, Clone, Copy, Debug, PartialEq)]
#[repr(u32)]
pub enum InstructionOp {
    // Binary
    Add = 0,
    Sub,
    Mul,
    Div,
    Pow,
    Or,
    And,
    Eq,
    Ne,
    Ge,
    Gt,
    Le,
    Lt,
    BitOr,
    BitAnd,
    BitXor,
    Shr,
    ShrSigned,
    Shl,
    Mod,

    // Unary
    Not,
    Negate,
    BitNot,

    // Cast
    // Cast,

    // Arrays
    ArrayInitRepeat,
    ArrayInit,
    ArrayIndexGet,
    ArraySliceGet,
    ArrayIndexStore,
    ArraySliceStore,

    // Tuples
    TupleInit,
    TupleIndexGet,
    TupleIndexStore,

    // Complex Expressions
    Pick,
    Mask,
    Repeat,

    // Variables
    Store,

    // Function Call
    Call,
    Return,

    // Debugging
    Assert,
    Log,

    // FFI/Core
    CallCore,
}
