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
use snarkvm_circuits::{Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use snarkvm_circuits::{Aleo, Field, Literal, ToFields};
use std::io::{Read, Result as IoResult, Write};

/// Performs a Poseidon hash with an input rate of 2.
pub struct HashPsd2<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> HashPsd2<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for HashPsd2<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "hash.psd2"
    }
}

impl<P: Program> Parser for HashPsd2<P> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for HashPsd2<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for HashPsd2<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for HashPsd2<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for HashPsd2<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::HashPsd2(self)
    }
}

impl<P: Program> Operation<P> for HashPsd2<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        impl_poseidon_evaluate!(self, registers);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.psd2 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPsd2(_)));
    }

    test_modes!(
        field,
        HashPsd2,
        "1field",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i8,
        HashPsd2,
        "1i8",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i16,
        HashPsd2,
        "1i16",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i32,
        HashPsd2,
        "1i32",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i64,
        HashPsd2,
        "1i64",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        i128,
        HashPsd2,
        "1i128",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u8,
        HashPsd2,
        "1u8",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u16,
        HashPsd2,
        "1u16",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u32,
        HashPsd2,
        "1u32",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u64,
        HashPsd2,
        "1u64",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        u128,
        HashPsd2,
        "1u128",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        scalar,
        HashPsd2,
        "1scalar",
        "895920223209807336032370141805192618496779881680412280727415085489332840844field"
    );
    test_modes!(
        string,
        HashPsd2,
        "\"aaaaaaaa\"",
        "3304929462283992873125391937087251720796648284457823938893125121531366375892field"
    );

    test_instruction_halts!(bool_halts, HashPsd2, "Invalid 'hash.psd2' instruction", "true");
    test_instruction_halts!(
        address_halts,
        HashPsd2,
        "Invalid 'hash.psd2' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(group_halts, HashPsd2, "Invalid 'hash.psd2' instruction", "2group");

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPsd2::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "2583689449389277015190969270607405416361985601581282452547069127520564162726field.private",
        );
        assert_eq!(expected, value);
    }
}
