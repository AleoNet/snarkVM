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

use super::Hash;
use crate::function::Opcode;

/// Performs a Pedersen hash taking a 256-bit value as input.
pub type HashPed256<P> = Hash<P, Pedersen256Hasher>;

pub struct Pedersen256Hasher;

impl Opcode for Pedersen256Hasher {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "hash.ped256"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        function::{Instruction, Operation, Registers},
        test_instruction_halts,
        test_modes,
        Identifier,
        Process,
        Register,
        Value,
    };
    use snarkvm_circuits::{Literal, Parser};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped256 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed256(_)));
    }

    test_modes!(
        address,
        HashPed256,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "7481826612753713410217729925917351756348444555753582640939800395433217644869field"
    );
    test_modes!(
        bool,
        HashPed256,
        "true",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        field,
        HashPed256,
        "1field",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        group,
        HashPed256,
        "2group",
        "564546604862166251269187547407669874296117017437472033102698766525356841251field"
    );
    test_modes!(
        i8,
        HashPed256,
        "1i8",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i16,
        HashPed256,
        "1i16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i32,
        HashPed256,
        "1i32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i64,
        HashPed256,
        "1i64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i128,
        HashPed256,
        "1i128",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u8,
        HashPed256,
        "1u8",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u16,
        HashPed256,
        "1u16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u32,
        HashPed256,
        "1u32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u64,
        HashPed256,
        "1u64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u128,
        HashPed256,
        "1u128",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        scalar,
        HashPed256,
        "1scalar",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        string,
        HashPed256,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "8063314925684455390425942164298513603090905455616863617234977954221147821673field"
    );

    test_instruction_halts!(
        string_halts,
        HashPed256,
        "The Pedersen hash input cannot exceed 256 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("true.public"),
            Literal::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed256::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "6122249396247477588925765696834100286827340493907798245233656838221917119242field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 256 bits.")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed256::from_str("r0 into r1").evaluate(&registers);
    }
}
