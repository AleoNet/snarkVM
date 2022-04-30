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

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    helpers::Register,
    impl_instruction_boilerplate,
    Program,
    Value,
};
use snarkvm_circuits::{Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Performs a Pedersen hash taking a 64-bit value as input.
pub struct Ped64<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Ped64, UnaryOperation, "hash.ped64");

impl_hash_instruction!(Ped64);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

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
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );
    test_modes!(i8, Ped64, "1i8", "7196659803296294243777457885733673378668319525819811655288865404872703603579field");
    test_modes!(
        i16,
        Ped64,
        "1i16",
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );
    test_modes!(
        i32,
        Ped64,
        "1i32",
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );
    test_modes!(
        i64,
        Ped64,
        "1i64",
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );
    test_modes!(u8, Ped64, "1u8", "7196659803296294243777457885733673378668319525819811655288865404872703603579field");
    test_modes!(
        u16,
        Ped64,
        "1u16",
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );
    test_modes!(
        u32,
        Ped64,
        "1u32",
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );
    test_modes!(
        u64,
        Ped64,
        "1u64",
        "7196659803296294243777457885733673378668319525819811655288865404872703603579field"
    );

    test_instruction_halts!(
        address_halts,
        Ped64,
        "Invalid input size for Pedersen64 hash",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
    );
    test_instruction_halts!(field_halts, Ped64, "Invalid input size for Pedersen64 hash", "1field");
    test_instruction_halts!(group_halts, Ped64, "Invalid input size for Pedersen64 hash", "2group");
    test_instruction_halts!(scalar_halts, Ped64, "Invalid input size for Pedersen64 hash", "1scalar");
    test_instruction_halts!(i128_halts, Ped64, "Invalid input size for Pedersen64 hash", "1i128");
    test_instruction_halts!(u128_halts, Ped64, "Invalid input size for Pedersen64 hash", "1u128");
}
