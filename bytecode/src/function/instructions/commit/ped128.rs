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

/// Performs a Pedersen commitment taking a 128-bit value as input.
pub struct PedComm128<P: Program> {
    operation: BinaryOperation<P>,
}

impl_instruction_boilerplate!(PedComm128, BinaryOperation, "commit.ped128");

impl_commit_instruction!(PedComm128);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped128 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::PedComm128(_)));
    }

    test_modes!(
        bool,
        PedComm128,
        "true",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i8,
        PedComm128,
        "1i8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i16,
        PedComm128,
        "1i16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i32,
        PedComm128,
        "1i32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i64,
        PedComm128,
        "1i64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i128,
        PedComm128,
        "1i128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u8,
        PedComm128,
        "1u8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u16,
        PedComm128,
        "1u16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u32,
        PedComm128,
        "1u32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u64,
        PedComm128,
        "1u64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u128,
        PedComm128,
        "1u128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        string,
        PedComm128,
        "\"aaaaaaaaaaaaaaaa\"",
        "1scalar",
        "379417118045898520789123124736668719236348888564273665391158449346246489573group"
    );

    test_instruction_halts!(
        address_halts,
        PedComm128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar"
    );
    test_instruction_halts!(
        field_halts,
        PedComm128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "1field",
        "1scalar"
    );
    test_instruction_halts!(
        group_halts,
        PedComm128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "2group",
        "1scalar"
    );
    test_instruction_halts!(
        scalar_halts,
        PedComm128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "1scalar",
        "1scalar"
    );
    test_instruction_halts!(
        string_halts,
        PedComm128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "\"aaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );
}
