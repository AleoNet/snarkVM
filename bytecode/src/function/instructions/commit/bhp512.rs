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

/// Performs a Pedersen commitment taking a 512-bit value as input.
pub type CommitBHP512<P> = Commit<P, BHP512>;

pub struct BHP512;
impl CommitOpcode for BHP512 {
    const OPCODE: &'static str = "commit.bhp512";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.bhp512 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitBHP512(_)));
    }

    test_modes!(
        address,
        CommitBHP512,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "1024999587065222757815020176635139198611915336169136252754321184462240177811field"
    );
    test_modes!(
        field,
        CommitBHP512,
        "1field",
        "1scalar",
        "2083013971163940182211664051244957344819949897366942786697993728427059271410field"
    );
    test_modes!(
        group,
        CommitBHP512,
        "2group",
        "1scalar",
        "4760377266890736367187296988047377035529414614183067393001507885670459356683field"
    );
    test_modes!(
        string,
        CommitBHP512,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "338950122786510723600799178077474673067268746738956264227399967753982657647field"
    );
    test_modes!(
        scalar,
        CommitBHP512,
        "1scalar",
        "1scalar",
        "7134326547462512190562098485578970108199343808208118290027699514070538132004field"
    );

    test_instruction_halts!(
        bool_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "true",
        "1scalar"
    );
    test_instruction_halts!(
        i8_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i8",
        "1scalar"
    );
    test_instruction_halts!(
        i16_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i16",
        "1scalar"
    );
    test_instruction_halts!(
        i32_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i32",
        "1scalar"
    );
    test_instruction_halts!(
        i64_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i64",
        "1scalar"
    );
    test_instruction_halts!(
        i128_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1i128",
        "1scalar"
    );
    test_instruction_halts!(
        u8_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u8",
        "1scalar"
    );
    test_instruction_halts!(
        u16_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u16",
        "1scalar"
    );
    test_instruction_halts!(
        u32_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u32",
        "1scalar"
    );
    test_instruction_halts!(
        u64_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u64",
        "1scalar"
    );
    test_instruction_halts!(
        u128_halts,
        CommitBHP512,
        "Inputs to this BHP variant must be greater than 171 bits",
        "1u128",
        "1scalar"
    );
    test_instruction_halts!(
        string_halts,
        CommitBHP512,
        "Inputs to this BHP variant cannot exceed 513 bits",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );

    #[test]
    fn test_composite() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
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

        CommitBHP512::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "2083013971163940182211664051244957344819949897366942786697993728427059271410field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 513 bits")]
    fn test_composite_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
            Literal::from_str("3field.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitBHP512::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
