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
    Program,
    Value,
};
use snarkvm_circuits::{Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use std::io::{Read, Result as IoResult, Write};

/// Performs a Pedersen hash taking a 256-bit value as input.
pub struct Ped256<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Ped256, UnaryOperation, "hash.ped256");

impl_hash_instruction!(Ped256);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped256 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Ped256(_)));
    }

    test_modes!(
        bool,
        Ped256,
        "true",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        field,
        Ped256,
        "1field",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(i8, Ped256, "1i8", "1059262140582054646087442833529957293574844959777794341556707461365918592080field");
    test_modes!(
        i16,
        Ped256,
        "1i16",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        i32,
        Ped256,
        "1i32",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        i64,
        Ped256,
        "1i64",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        i128,
        Ped256,
        "1i128",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(u8, Ped256, "1u8", "1059262140582054646087442833529957293574844959777794341556707461365918592080field");
    test_modes!(
        u16,
        Ped256,
        "1u16",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        u32,
        Ped256,
        "1u32",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        u64,
        Ped256,
        "1u64",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        u128,
        Ped256,
        "1u128",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        scalar,
        Ped256,
        "1scalar",
        "1059262140582054646087442833529957293574844959777794341556707461365918592080field"
    );
    test_modes!(
        string,
        Ped256,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "2632508552150990423544074948282833192127170425169355729866531836863371536481field"
    );

    test_instruction_halts!(
        address_halts,
        Ped256,
        "Invalid input size for Pedersen256 hash",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(group_halts, Ped256, "Invalid input size for Pedersen256 hash", "2group");
    test_instruction_halts!(
        string_halts,
        Ped256,
        "Invalid input size for Pedersen256 hash",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );
}
