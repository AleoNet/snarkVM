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

/// Performs a Pedersen commitment taking a 64-bit value as input.
pub struct PedComm64<P: Program> {
    operation: BinaryOperation<P>,
}

impl_instruction_boilerplate!(PedComm64, BinaryOperation, "commit.ped64");

impl_commit_instruction!(PedComm64);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped64 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::PedComm64(_)));
    }

    test_modes!(
        bool,
        PedComm64,
        "true",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i8,
        PedComm64,
        "1i8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i16,
        PedComm64,
        "1i16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i32,
        PedComm64,
        "1i32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i64,
        PedComm64,
        "1i64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u8,
        PedComm64,
        "1u8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u16,
        PedComm64,
        "1u16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u32,
        PedComm64,
        "1u32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u64,
        PedComm64,
        "1u64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        string,
        PedComm64,
        "\"aaaaaaaa\"",
        "1scalar",
        "3676661776668839972619997881903122186869024107388712238481736297789602888074group"
    );

    test_instruction_halts!(
        address_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar"
    );
    test_instruction_halts!(
        field_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1field",
        "1scalar"
    );
    test_instruction_halts!(
        group_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "2group",
        "1scalar"
    );
    test_instruction_halts!(
        scalar_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1scalar",
        "1scalar"
    );
    test_instruction_halts!(
        i128_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1i128",
        "1scalar"
    );
    test_instruction_halts!(
        u128_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "1u128",
        "1scalar"
    );
    test_instruction_halts!(
        string_halts,
        PedComm64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "\"aaaaaaaaa\"",
        "1scalar"
    );
}
