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

/// Performs a Pedersen hash taking a 64-bit value as input.
pub struct Ped64<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Ped64, UnaryOperation, "hash.ped64");

impl_hash_instruction!(Ped64);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped64 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Ped64(_)));
    }

    test_modes!(
        bool,
        Ped64,
        "true",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(i8, Ped64, "1i8", "6122249396247477588925765696834100286827340493907798245233656838221917119242field");
    test_modes!(
        i16,
        Ped64,
        "1i16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i32,
        Ped64,
        "1i32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i64,
        Ped64,
        "1i64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(u8, Ped64, "1u8", "6122249396247477588925765696834100286827340493907798245233656838221917119242field");
    test_modes!(
        u16,
        Ped64,
        "1u16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u32,
        Ped64,
        "1u32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u64,
        Ped64,
        "1u64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        string,
        Ped64,
        "\"aaaaaaaa\"",
        "7299801179261936372670032123063256554706653150313868761081445373623581679329field"
    );

    test_instruction_halts!(
        address_halts,
        Ped64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(field_halts, Ped64, "The Pedersen hash input cannot exceed 64 bits.", "1field");
    test_instruction_halts!(group_halts, Ped64, "The Pedersen hash input cannot exceed 64 bits.", "2group");
    test_instruction_halts!(scalar_halts, Ped64, "The Pedersen hash input cannot exceed 64 bits.", "1scalar");
    test_instruction_halts!(i128_halts, Ped64, "The Pedersen hash input cannot exceed 64 bits.", "1i128");
    test_instruction_halts!(u128_halts, Ped64, "The Pedersen hash input cannot exceed 64 bits.", "1u128");
    test_instruction_halts!(string_halts, Ped64, "The Pedersen hash input cannot exceed 64 bits.", "\"aaaaaaaaa\"");

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

        Ped64::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "6122249396247477588925765696834100286827340493907798245233656838221917119242field.private",
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

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        Ped64::from_str("r0 into r1").evaluate(&registers);
    }
}
