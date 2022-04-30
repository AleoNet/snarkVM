// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    helpers::Register,
    Program,
    Value,
};
use snarkvm_circuits::{Literal, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Negates `first`, storing the outcome in `destination`.
pub struct Neg<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Neg, UnaryOperation, "neg");

impl<P: Program> Operation<P> for Neg<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        // Load the values for the first and second operands.
        let first = match registers.load(self.operation.first()) {
            Value::Literal(literal) => literal,
            Value::Composite(name, ..) => P::halt(format!("{name} is not a literal")),
        };

        // Perform the operation.
        let result = match first {
            Literal::Field(a) => Literal::Field(-a),
            Literal::Group(a) => Literal::Group(-a),
            Literal::I8(a) => Literal::I8(-a),
            Literal::I16(a) => Literal::I16(-a),
            Literal::I32(a) => Literal::I32(-a),
            Literal::I64(a) => Literal::I64(-a),
            Literal::I128(a) => Literal::I128(-a),
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        };

        registers.assign(self.operation.destination(), result);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<Process>::parse("neg r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Neg(_)));
    }

    test_modes!(field, Neg, "1field", "-1field");
    test_modes!(group, Neg, "2group", "-2group");
    test_modes!(i8, Neg, "1i8", "-1i8");
    test_modes!(i16, Neg, "1i16", "-1i16");
    test_modes!(i32, Neg, "1i32", "-1i32");
    test_modes!(i64, Neg, "1i64", "-1i64");
    test_modes!(i128, Neg, "1i128", "-1i128");

    test_instruction_halts!(
        i8_min_neg_halts,
        Neg,
        "Integer overflow on addition of two constants",
        &format!("{}i8", i8::MIN)
    );
    test_instruction_halts!(
        i16_min_neg_halts,
        Neg,
        "Integer overflow on addition of two constants",
        &format!("{}i16", i16::MIN)
    );
    test_instruction_halts!(
        i32_min_neg_halts,
        Neg,
        "Integer overflow on addition of two constants",
        &format!("{}i32", i32::MIN)
    );
    test_instruction_halts!(
        i64_min_neg_halts,
        Neg,
        "Integer overflow on addition of two constants",
        &format!("{}i64", i64::MIN)
    );
    test_instruction_halts!(
        i128_min_neg_halts,
        Neg,
        "Integer overflow on addition of two constants",
        &format!("{}i128", i128::MIN)
    );
    test_instruction_halts!(u8_neg_halts, Neg, "Invalid 'neg' instruction", "1u8");
    test_instruction_halts!(u16_neg_halts, Neg, "Invalid 'neg' instruction", "1u16");
    test_instruction_halts!(u32_neg_halts, Neg, "Invalid 'neg' instruction", "1u32");
    test_instruction_halts!(u64_neg_halts, Neg, "Invalid 'neg' instruction", "1u64");
    test_instruction_halts!(u128_neg_halts, Neg, "Invalid 'neg' instruction", "1u128");
    test_instruction_halts!(scalar_neg_halts, Neg, "Invalid 'neg' instruction", "1scalar.constant");
    test_instruction_halts!(
        address_neg_halts,
        Neg,
        "Invalid 'neg' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(boolean_neg_halts, Neg, "Invalid 'neg' instruction", "true.constant");
    test_instruction_halts!(string_neg_halts, Neg, "Invalid 'neg' instruction", "\"hello\".constant");
}
