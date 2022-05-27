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

use super::*;

/// Performs a BHP hash taking up to a 1024-bit value as input.
pub type HashBHP1024<P> = Hash<P, BHP1024>;

pub struct BHP1024;
impl HashOpcode for BHP1024 {
    const OPCODE: &'static str = "hash.bhp1024";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Register, Registers},
        test_instruction_halts,
        test_modes,
        Identifier,
        Process,
        Value,
    };
    use snarkvm_circuits::Parser;

    type P = Process;

    #[ignore]
    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.bhp1024 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashBHP1024(_)));
    }

    test_modes!(
        address,
        HashBHP1024,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "5444329435182671516961120056231218765809269544095568309770443334177521411623field"
    );
    test_modes!(
        field,
        HashBHP1024,
        "1field",
        "349959275141959883733705261399296435764872842479947121120258093248412848615field"
    );
    test_modes!(
        group,
        HashBHP1024,
        "2group",
        "1774757514576748925701633562510423405839978849182774441663017589974158335041field"
    );
    test_modes!(
        scalar,
        HashBHP1024,
        "1scalar",
        "3686659870323391476089546091421288046448055273023150326715307288276673327545field"
    );
    test_modes!(
        string,
        HashBHP1024,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "8174246013303659340855191060112918869049649251129173464957647709007353208767field"
    );

    test_instruction_halts!(
        bool_halts,
        HashBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "true"
    );
    test_instruction_halts!(i8_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1i8");
    test_instruction_halts!(i16_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1i16");
    test_instruction_halts!(i32_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1i32");
    test_instruction_halts!(i64_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1i64");
    test_instruction_halts!(
        i128_halts,
        HashBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i128"
    );
    test_instruction_halts!(u8_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1u8");
    test_instruction_halts!(u16_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1u16");
    test_instruction_halts!(u32_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1u32");
    test_instruction_halts!(u64_halts, HashBHP1024, "Inputs to this BHP variant must be greater than 171 bits", "1u64");
    test_instruction_halts!(
        u128_halts,
        HashBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u128"
    );
    test_instruction_halts!(
        string_halts,
        HashBHP1024,
        "Inputs to this BHP variant cannot exceed 1026 bits",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[ignore]
    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP1024::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "4899825579676170066989655542341882152621291668615292090582612568617586716417field.private",
        );
        assert_eq!(expected, value);
    }

    #[ignore]
    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 1026 bits")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("2field.private"),
            Value::from_str("3field.private"),
            Value::from_str("4field.private"),
            Value::from_str("5field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashBHP1024::from_str("r0 into r1").evaluate(&registers);
    }
}
