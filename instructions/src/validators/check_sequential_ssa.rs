// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{Instruction, Program, Type};
use std::{fmt, fmt::Formatter};

// TODO (@pranav) Consider aggregating errors in an enum.
#[derive(Debug, Clone)]
pub struct SSAError {
    instruction_id: usize,
    typ: Type,
}

impl fmt::Display for SSAError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Non-sequential SSA for {:?} at instruction #{:?}", self.typ, self.instruction_id)
    }
}

// TODO (@pranav) Clean up implementation. Currently a rough prototype.
pub fn check_sequential_ssa(program: &Program) -> Result<(), SSAError> {
    let mut next_base_field_register: u64 = 0;
    let mut next_boolean_register: u64 = 0;
    let mut next_group_register: u64 = 0;
    let mut next_i8_register: u64 = 0;
    let mut next_i16_register: u64 = 0;
    let mut next_i32_register: u64 = 0;
    let mut next_i64_register: u64 = 0;
    let mut next_i128_register: u64 = 0;
    let mut next_u8_register: u64 = 0;
    let mut next_u16_register: u64 = 0;
    let mut next_u32_register: u64 = 0;
    let mut next_u64_register: u64 = 0;
    let mut next_u128_register: u64 = 0;
    let mut next_scalar_field_register: u64 = 0;

    for instruction in &program.instructions {
        for register in &instruction.destinations {
            // Helper to check and increment register counts.
            let check_register = |counter: &mut u64| {
                if *counter == register.id {
                    *counter += 1;
                    Ok(())
                } else {
                    Err(SSAError { instruction_id: register.id as usize, typ: register.typ })
                }
            };

            match register.typ {
                Type::BaseField => check_register(&mut next_base_field_register),
                Type::Boolean => check_register(&mut next_boolean_register),
                Type::Group => check_register(&mut next_group_register),
                Type::I8 => check_register(&mut next_i8_register),
                Type::I16 => check_register(&mut next_i16_register),
                Type::I32 => check_register(&mut next_i32_register),
                Type::I64 => check_register(&mut next_i64_register),
                Type::I128 => check_register(&mut next_i128_register),
                Type::ScalarField => check_register(&mut next_scalar_field_register),
                Type::U8 => check_register(&mut next_u8_register),
                Type::U16 => check_register(&mut next_u16_register),
                Type::U32 => check_register(&mut next_u32_register),
                Type::U64 => check_register(&mut next_u64_register),
                Type::U128 => check_register(&mut next_u128_register),
            }?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_sequential_ssa_valid() {
        let (input, program) = Program::new(
            "u8.r0 := addw.u8 0u8, 1u8;\n\
                   u8.r1 := addw.u8 0u8, 2u8;\n\
                   bool.r0 := eq.u8 u8.r0, u8.r1;",
        )
        .unwrap();
        assert!(check_sequential_ssa(&program).is_ok());
    }

    #[test]
    fn test_sequential_ssa_invalid() {
        let (input, program) = Program::new(
            "u8.r3 := addw.u8 u8.r2, u8.r1;\n\
                   u8.r6 := addw.u8 u8.r5, u8.r4;\n\
                   bool.r1 := eq.u8 u8.r5, u8.r6;",
        )
        .unwrap();
        assert!(check_sequential_ssa(&program).is_err());
    }
}
