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

/// Performs a Pedersen commitment taking a 256-bit value as input.
pub type CommitPed256<P> = Commit<P, Ped256>;

pub struct Ped256;
impl CommitOpcode for Ped256 {
    const OPCODE: &'static str = "commit.ped256";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{function::Register, test_instruction_halts, test_modes, Identifier, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped256 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed256(_)));
    }

    test_modes!(
        address,
        CommitPed256,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "3209171340981864543266405414366060789110320385800446890741891373278205263346field"
    );
    test_modes!(
        bool,
        CommitPed256,
        "true",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        field,
        CommitPed256,
        "1field",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        group,
        CommitPed256,
        "2group",
        "1scalar",
        "7526860243782102044430898702968287626100250324788799205880305445717943584221field"
    );
    test_modes!(
        i8,
        CommitPed256,
        "1i8",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        i16,
        CommitPed256,
        "1i16",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        i32,
        CommitPed256,
        "1i32",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        i64,
        CommitPed256,
        "1i64",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        i128,
        CommitPed256,
        "1i128",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        u8,
        CommitPed256,
        "1u8",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        u16,
        CommitPed256,
        "1u16",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        u32,
        CommitPed256,
        "1u32",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        u64,
        CommitPed256,
        "1u64",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        u128,
        CommitPed256,
        "1u128",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );
    test_modes!(
        string,
        CommitPed256,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "1697784346568291403184339111119715631403741153760855419498239551653716695642field"
    );
    test_modes!(
        scalar,
        CommitPed256,
        "1scalar",
        "1scalar",
        "478157451423847009900236798818848382990838648975907384417461239031072256563field"
    );

    test_instruction_halts!(
        string_halts,
        CommitPed256,
        "The Pedersen hash input cannot exceed 256 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("true.public"),
            Value::from_str("false.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed256::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "19341056535717425085758329792683924877273194890858381597697503538688102493field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 256 bits.")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1field.public"),
            Value::from_str("2field.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed256::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
