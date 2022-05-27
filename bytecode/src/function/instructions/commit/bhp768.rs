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

/// Performs a Pedersen commitment taking a 768-bit value as input.
pub type CommitBHP768<P> = Commit<P, BHP768>;

pub struct BHP768;
impl CommitOpcode for BHP768 {
    const OPCODE: &'static str = "commit.bhp768";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{function::Register, Identifier, Process};

    type P = Process;

    #[ignore]
    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.bhp768 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitBHP768(_)));
    }

    // test_modes!(
    //     address,
    //     CommitBHP768,
    //     "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
    //     "1scalar",
    //     "7805232804326319384586713838835822785368523800929919909882340889083523011715field"
    // );
    // test_modes!(
    //     field,
    //     CommitBHP768,
    //     "1field",
    //     "1scalar",
    //     "7557176215516480491199520827195710815598751787835606394250163515532521646538field"
    // );
    // test_modes!(
    //     group,
    //     CommitBHP768,
    //     "2group",
    //     "1scalar",
    //     "83678373235481120609615966891945250382503097807456666235229083614007049268field"
    // );
    // test_modes!(
    //     string,
    //     CommitBHP768,
    //     "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
    //     "1scalar",
    //     "7332172440045149977203590215103044723646488199043272011926588398495503285703field"
    // );
    // test_modes!(
    //     scalar,
    //     CommitBHP768,
    //     "1scalar",
    //     "1scalar",
    //     "7334642676686871805322582421038201806170812369288870248390938977964678660641field"
    // );
    //
    // test_instruction_halts!(
    //     bool_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "true",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i8_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i8",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i16_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i16",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i32_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i32",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i64_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i64",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i128_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i128",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u8_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u8",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u16_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u16",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u32_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u32",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u64_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u64",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u128_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u128",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     string_halts,
    //     CommitBHP768,
    //     "Inputs to this BHP variant cannot exceed 774 bits",
    //     "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
    //     "1scalar"
    // );

    #[ignore]
    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("false.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitBHP768::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "5899428566576950341837391336369600491245501981868562030593082410292718439978field.private",
        );
        assert_eq!(expected, value);
    }

    #[ignore]
    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 774 bits")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("2field.private"),
            Value::from_str("3field.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitBHP768::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
