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

/// Performs a Pedersen hash taking a 512-bit value as input.
pub struct Ped512<P: Program> {
    operation: UnaryOperation<P>,
}

impl_instruction_boilerplate!(Ped512, UnaryOperation, "hash.ped512");

impl_hash_instruction!(Ped512);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped512 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::Ped512(_)));
    }

    test_modes!(
        address,
        Ped512,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "3291626649400662662682375267972202839775158707500840171547444686699260553443field"
    );
    test_modes!(
        bool,
        Ped512,
        "true",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        field,
        Ped512,
        "1field",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        group,
        Ped512,
        "2group",
        "6465529375167943116297563421359589501761966597307192826832026345697026207621field"
    );
    test_modes!(i8, Ped512, "1i8", "5650135281756419312758994095254830176594411601263690120533705951569309252815field");
    test_modes!(
        i16,
        Ped512,
        "1i16",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        i32,
        Ped512,
        "1i32",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        i64,
        Ped512,
        "1i64",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        i128,
        Ped512,
        "1i128",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(u8, Ped512, "1u8", "5650135281756419312758994095254830176594411601263690120533705951569309252815field");
    test_modes!(
        u16,
        Ped512,
        "1u16",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        u32,
        Ped512,
        "1u32",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        u64,
        Ped512,
        "1u64",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        u128,
        Ped512,
        "1u128",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        scalar,
        Ped512,
        "1scalar",
        "5650135281756419312758994095254830176594411601263690120533705951569309252815field"
    );
    test_modes!(
        string,
        Ped512,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "8389342203483798400493397615966516498056188500240673235751281002336191843595field"
    );

    test_instruction_halts!(
        string_halts,
        Ped512,
        "Invalid input size for Pedersen512 hash",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
    );
}
