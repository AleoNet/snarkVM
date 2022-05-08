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

/// Performs a Pedersen hash taking up to a 64-bit value as input.
pub type HashPed64<P> = Hash<P, Ped64>;

pub struct Ped64;
impl HashOpcode for Ped64 {
    const OPCODE: &'static str = "hash.ped64";
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
    use snarkvm_circuits::{Literal, Parser};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped64 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed64(_)));
    }

    test_modes!(
        bool,
        HashPed64,
        "true",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        i8,
        HashPed64,
        "1i8",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        i16,
        HashPed64,
        "1i16",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        i32,
        HashPed64,
        "1i32",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        i64,
        HashPed64,
        "1i64",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        u8,
        HashPed64,
        "1u8",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        u16,
        HashPed64,
        "1u16",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        u32,
        HashPed64,
        "1u32",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        u64,
        HashPed64,
        "1u64",
        "4824894454396053096074107021690044320571663539657536391321141410576222777405field"
    );
    test_modes!(
        string,
        HashPed64,
        "\"aaaaaaaa\"",
        "8062121933923095963178939309677821353130128054929572359569040131401401332970field"
    );

    test_instruction_halts!(
        address_halts,
        HashPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(field_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1field");
    test_instruction_halts!(group_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "2group");
    test_instruction_halts!(scalar_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1scalar");
    test_instruction_halts!(i128_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1i128");
    test_instruction_halts!(u128_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1u128");
    test_instruction_halts!(string_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "\"aaaaaaaaa\"");

    #[test]
    fn test_definition() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("true.public").into(),
            Literal::from_str("false.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed64::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "1165733009942080909002488939916331167249630034847646106762047794931549397383field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 64 bits.")]
    fn test_definition_halts() {
        let first = Value::<P>::Definition(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public").into(),
            Literal::from_str("false.private").into(),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed64::from_str("r0 into r1").evaluate(&registers);
    }
}
