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

/// Performs a Pedersen hash taking a 1024-bit value as input.
pub struct Ped1024<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Ped1024, UnaryOperation, "hash.ped1024");

impl_hash_instruction!(Ped1024);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped1024 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Ped1024(_)));
    }

    test_modes!(
        address,
        Ped1024,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1702909397913101796114358591597241111178777838134197312676975239197295270132field"
    );
    test_modes!(
        bool,
        Ped1024,
        "true",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        field,
        Ped1024,
        "1field",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        group,
        Ped1024,
        "2group",
        "8070237331084410774593421518031669626821616288000571831752204940857622128794field"
    );
    test_modes!(
        i8,
        Ped1024,
        "1i8",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        i16,
        Ped1024,
        "1i16",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        i32,
        Ped1024,
        "1i32",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        i64,
        Ped1024,
        "1i64",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        i128,
        Ped1024,
        "1i128",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        u8,
        Ped1024,
        "1u8",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        u16,
        Ped1024,
        "1u16",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        u32,
        Ped1024,
        "1u32",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        u64,
        Ped1024,
        "1u64",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        u128,
        Ped1024,
        "1u128",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        scalar,
        Ped1024,
        "1scalar",
        "2735878956944204282034515986614586323780043889637881845468543426547714835261field"
    );
    test_modes!(
        string,
        Ped1024,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "4823687538796085678706395592605314872047221564256175161093057716327805678675field"
    );

    test_instruction_halts!(
        string_halts,
        Ped1024,
        "Invalid input size for Pedersen1024 hash",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );
}
