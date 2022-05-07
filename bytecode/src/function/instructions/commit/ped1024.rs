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
pub type CommitPed1024<P> = Commit<P, Ped1024>;

pub struct Ped1024;
impl CommitOpcode for Ped1024 {
    const OPCODE: &'static str = "commit.ped1024";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped1024 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed1024(_)));
    }

    test_modes!(
        address,
        CommitPed1024,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "1934730463123157804333109559051649344049874813284474563323837880134504789364group"
    );
    test_modes!(
        bool,
        CommitPed1024,
        "true",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        field,
        CommitPed1024,
        "1field",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        group,
        CommitPed1024,
        "2group",
        "1scalar",
        "3778525580012649091303886415665817219951782658607058820875192622123135493867group"
    );
    test_modes!(
        i8,
        CommitPed1024,
        "1i8",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        i16,
        CommitPed1024,
        "1i16",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        i32,
        CommitPed1024,
        "1i32",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        i64,
        CommitPed1024,
        "1i64",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        i128,
        CommitPed1024,
        "1i128",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        u8,
        CommitPed1024,
        "1u8",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        u16,
        CommitPed1024,
        "1u16",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        u32,
        CommitPed1024,
        "1u32",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        u64,
        CommitPed1024,
        "1u64",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        u128,
        CommitPed1024,
        "1u128",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );
    test_modes!(
        string,
        CommitPed1024,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "4771372094013743157322025472946439349851832167617775669085073448656629178103group"
    );
    test_modes!(
        scalar,
        CommitPed1024,
        "1scalar",
        "1scalar",
        "813626960646411069805793722601785921190040983449007340699428340976262249510group"
    );

    test_instruction_halts!(
        string_halts,
        CommitPed1024,
        "The Pedersen hash input cannot exceed 1024 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
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

        CommitPed1024::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "813626960646411069805793722601785921190040983449007340699428340976262249510group.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 1024 bits.")]
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

        CommitPed1024::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
