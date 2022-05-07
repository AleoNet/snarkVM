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

/// Performs a Pedersen commitment taking a 64-bit value as input.
pub type CommitPed64<P> = Commit<P, Ped64>;

pub struct Ped64;
impl CommitOpcode for Ped64 {
    const OPCODE: &'static str = "commit.ped64";
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped64 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed64(_)));
    }

    test_modes!(
        bool,
        CommitPed64,
        "true",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        i8,
        CommitPed64,
        "1i8",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        i16,
        CommitPed64,
        "1i16",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        i32,
        CommitPed64,
        "1i32",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        i64,
        CommitPed64,
        "1i64",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        u8,
        CommitPed64,
        "1u8",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        u16,
        CommitPed64,
        "1u16",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        u32,
        CommitPed64,
        "1u32",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        u64,
        CommitPed64,
        "1u64",
        "1scalar",
        "451816983925465612310036142898649792841141971816913349341750601484549023437field"
    );
    test_modes!(
        string,
        CommitPed64,
        "\"aaaaaaaa\"",
        "1scalar",
        "5622478747945370229693309401233561591542417534378600804836808353744293560079field"
    );

    test_instruction_halts!(
        address_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar"
    );
    test_instruction_halts!(
        field_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1field",
        "1scalar"
    );
    test_instruction_halts!(
        group_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "2group",
        "1scalar"
    );
    test_instruction_halts!(
        scalar_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1scalar",
        "1scalar"
    );
    test_instruction_halts!(
        i128_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1i128",
        "1scalar"
    );
    test_instruction_halts!(
        u128_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1u128",
        "1scalar"
    );
    test_instruction_halts!(
        string_halts,
        CommitPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "\"aaaaaaaaa\"",
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

        CommitPed64::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "451816983925465612310036142898649792841141971816913349341750601484549023437field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 64 bits.")]
    fn test_composite_halts() {
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

        CommitPed64::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
