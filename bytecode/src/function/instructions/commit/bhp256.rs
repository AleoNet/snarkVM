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
pub type CommitBHP256<P> = Commit<P, BHP256>;

pub struct BHP256;
impl CommitOpcode for BHP256 {
    const OPCODE: &'static str = "commit.bhp256";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{function::Register, Identifier, Process, Value};

    type P = Process;

    #[ignore]
    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.bhp256 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitBHP256(_)));
    }

    // test_modes!(
    //     address,
    //     CommitBHP256,
    //     "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
    //     "1scalar",
    //     "7115473038624331514996031744051806024254138485569634257977816499703872444569field"
    // );
    // test_modes!(
    //     field,
    //     CommitBHP256,
    //     "1field",
    //     "1scalar",
    //     "6735841589287481182565103554915497076009759637769041328115551207221718855772field"
    // );
    // test_modes!(
    //     group,
    //     CommitBHP256,
    //     "2group",
    //     "1scalar",
    //     "7617724828496146666541559434042213702391225573464917918454302407165937027497field"
    // );
    // test_modes!(
    //     string,
    //     CommitBHP256,
    //     "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
    //     "1scalar",
    //     "2694809639456905569799705473661530581681379938099220673322304992825952388274field"
    // );
    // test_modes!(
    //     scalar,
    //     CommitBHP256,
    //     "1scalar",
    //     "1scalar",
    //     "6302764182214251270384692971932650766342423070217486222582849034895511665081field"
    // );
    //
    // test_instruction_halts!(
    //     bool_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "true",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i8_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i8",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i16_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i16",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i32_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i32",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i64_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i64",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     i128_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1i128",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u8_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u8",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u16_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u16",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u32_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u32",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u64_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u64",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     u128_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant must be greater than 129 bits",
    //     "1u128",
    //     "1scalar"
    // );
    // test_instruction_halts!(
    //     string_halts,
    //     CommitBHP256,
    //     "Inputs to this BHP variant cannot exceed 258 bits",
    //     "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
    //     "1scalar"
    // );

    #[ignore]
    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Value::from_str("1u128.public"),
            Value::from_str("1u8.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitBHP256::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "7011990780899172191128348191856233471462848048463198251737807495501253122629field.private",
        );
        assert_eq!(expected, value);
    }

    #[ignore]
    #[test]
    #[should_panic(expected = "Inputs to this BHP variant cannot exceed 258 bits")]
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

        CommitBHP256::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
