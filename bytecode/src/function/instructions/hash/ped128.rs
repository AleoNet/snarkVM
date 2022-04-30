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

/// Performs a Pedersen hash taking a 128-bit value as input.
pub struct Ped128<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Ped128, UnaryOperation, "hash.ped128");

impl_hash_instruction!(Ped128);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped128 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Ped128(_)));
    }

    test_modes!(
        bool,
        Ped128,
        "true",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(i8, Ped128, "1i8", "6122249396247477588925765696834100286827340493907798245233656838221917119242field");
    test_modes!(
        i16,
        Ped128,
        "1i16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i32,
        Ped128,
        "1i32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i64,
        Ped128,
        "1i64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i128,
        Ped128,
        "1i128",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(u8, Ped128, "1u8", "6122249396247477588925765696834100286827340493907798245233656838221917119242field");
    test_modes!(
        u16,
        Ped128,
        "1u16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u32,
        Ped128,
        "1u32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u64,
        Ped128,
        "1u64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u128,
        Ped128,
        "1u128",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        string,
        Ped128,
        "\"aaaaaaaaaaaaaaaa\"",
        "7311018268372560359075957295142034348080722421845019162102517007114103429378field"
    );

    test_instruction_halts!(
        address_halts,
        Ped128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(field_halts, Ped128, "The Pedersen hash input cannot exceed 128 bits.", "1field");
    test_instruction_halts!(group_halts, Ped128, "The Pedersen hash input cannot exceed 128 bits.", "2group");
    test_instruction_halts!(scalar_halts, Ped128, "The Pedersen hash input cannot exceed 128 bits.", "1scalar");
    test_instruction_halts!(
        string_halts,
        Ped128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "\"aaaaaaaaaaaaaaaaaa\""
    );
}
