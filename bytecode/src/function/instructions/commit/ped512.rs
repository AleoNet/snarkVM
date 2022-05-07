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
pub type CommitPed512<P> = Commit<P, Ped512>;

pub struct Ped512;
impl CommitOpcode for Ped512 {
    const OPCODE: &'static str = "commit.ped512";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped512 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed512(_)));
    }

    test_modes!(
        address,
        CommitPed512,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "3410659255728169898750086325142668660454277499884743925718334122641396433696field"
    );
    test_modes!(
        bool,
        CommitPed512,
        "true",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        field,
        CommitPed512,
        "1field",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        group,
        CommitPed512,
        "2group",
        "1scalar",
        "3519938113542987815863571520168034497327536797778329828814521686527561395445field"
    );
    test_modes!(
        i8,
        CommitPed512,
        "1i8",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        i16,
        CommitPed512,
        "1i16",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        i32,
        CommitPed512,
        "1i32",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        i64,
        CommitPed512,
        "1i64",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        i128,
        CommitPed512,
        "1i128",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        u8,
        CommitPed512,
        "1u8",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        u16,
        CommitPed512,
        "1u16",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        u32,
        CommitPed512,
        "1u32",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        u64,
        CommitPed512,
        "1u64",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        u128,
        CommitPed512,
        "1u128",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );
    test_modes!(
        string,
        CommitPed512,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "2940548950498411855621626872089931006359864588508159785059887358076170748305field"
    );
    test_modes!(
        scalar,
        CommitPed512,
        "1scalar",
        "1scalar",
        "8207766802569749313965358209002972767463373090861921575237346864481239586165field"
    );

    test_instruction_halts!(
        string_halts,
        CommitPed512,
        "The Pedersen hash input cannot exceed 512 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("true.public"),
            Literal::from_str("false.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed512::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "8207766802569749313965358209002972767463373090861921575237346864481239586165field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 512 bits.")]
    fn test_definition_halts() {
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

        CommitPed512::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
