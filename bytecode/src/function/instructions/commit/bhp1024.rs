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

/// Performs a Pedersen commitment taking a 1024-bit value as input.
pub type CommitBHP1024<P> = Commit<P, BHP1024>;

pub struct BHP1024;
impl CommitOpcode for BHP1024 {
    const OPCODE: &'static str = "commit.bhp1024";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.bhp1024 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitBHP1024(_)));
    }

    test_modes!(
        address,
        CommitBHP1024,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "5169211120399519025986551670606780764013347455141509631890822048701323369186field"
    );
    test_modes!(
        field,
        CommitBHP1024,
        "1field",
        "1scalar",
        "6508586538017813241269740771062761903718479419650899989698274551452965779761field"
    );
    test_modes!(
        group,
        CommitBHP1024,
        "2group",
        "1scalar",
        "1294729523278578587871667172115457688354750567667093074165621715710049145003field"
    );
    test_modes!(
        string,
        CommitBHP1024,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "160489099302419323115427453404515625203514702014360959284944815999444413659field"
    );
    test_modes!(
        scalar,
        CommitBHP1024,
        "1scalar",
        "1scalar",
        "816331564773791261460396983911906817852823931737024567376324016383305772230field"
    );

    test_instruction_halts!(
        bool_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "true",
        "1scalar"
    );
    test_instruction_halts!(
        i8_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i8",
        "1scalar"
    );
    test_instruction_halts!(
        i16_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i16",
        "1scalar"
    );
    test_instruction_halts!(
        i32_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i32",
        "1scalar"
    );
    test_instruction_halts!(
        i64_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i64",
        "1scalar"
    );
    test_instruction_halts!(
        i128_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i128",
        "1scalar"
    );
    test_instruction_halts!(
        u8_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u8",
        "1scalar"
    );
    test_instruction_halts!(
        u16_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u16",
        "1scalar"
    );
    test_instruction_halts!(
        u32_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u32",
        "1scalar"
    );
    test_instruction_halts!(
        u64_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u64",
        "1scalar"
    );
    test_instruction_halts!(
        u128_halts,
        CommitBHP1024,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u128",
        "1scalar"
    );
    test_instruction_halts!(
        string_halts,
        CommitBHP1024,
        "Inputs to this BHP variant cannot exceed 1026 bits",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("false.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitBHP1024::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "6508586538017813241269740771062761903718479419650899989698274551452965779761field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 1026 bits")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
            Literal::from_str("3field.private"),
            Literal::from_str("4field.private"),
            Literal::from_str("5field.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitBHP1024::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
