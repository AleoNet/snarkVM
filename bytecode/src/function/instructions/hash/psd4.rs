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

/// Performs a Poseidon hash with an input rate of 4.
pub struct Psd4<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Psd4, UnaryOperation, "hash.psd4");

impl_psd_hash_instruction!(Psd4);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.psd4 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Psd4(_)));
    }

    test_modes!(
        field,
        Psd4,
        "1field",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(i8, Psd4, "1i8", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(i16, Psd4, "1i16", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(i32, Psd4, "1i32", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(i64, Psd4, "1i64", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(
        i128,
        Psd4,
        "1i128",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(u8, Psd4, "1u8", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(u16, Psd4, "1u16", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(u32, Psd4, "1u32", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(u64, Psd4, "1u64", "1088580045362314438112823188316979551898376415861015087020772893540491855029field");
    test_modes!(
        u128,
        Psd4,
        "1u128",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        scalar,
        Psd4,
        "1scalar",
        "1088580045362314438112823188316979551898376415861015087020772893540491855029field"
    );
    test_modes!(
        string,
        Psd4,
        "\"aaaaaaaa\"",
        "4167190024968967735724650291761534994019909311594675614398942316879984619698field"
    );

    test_instruction_halts!(bool_halts, Psd4, "Invalid 'hash.psd4' instruction", "true");
    test_instruction_halts!(
        address_halts,
        Psd4,
        "Invalid 'hash.psd4' instruction",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(group_halts, Psd4, "Invalid 'hash.psd4' instruction", "2group");
}
