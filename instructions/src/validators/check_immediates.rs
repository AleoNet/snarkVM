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

use crate::{Immediate, Operand, Program, Type};

use snarkvm_circuits::{Boolean, Environment};

use std::{fmt, fmt::Formatter, iter};

// TODO (@pranav) Consider aggregating errors in an enum.
#[derive(Debug, Clone)]
pub struct ImmediateParsingError {
    instruction_id: usize,
    typ: Type,
    value: String,
}

impl fmt::Display for ImmediateParsingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Unable to parse `{:?}` as {:?} at instruction #{:?}", self.value, self.typ, self.instruction_id)
    }
}

// TODO (@pranav) Clean up implementation. Currently a rough prototype.
//  - if-let vs match
//  - Error handling
pub fn check_immediates<E: Environment>(program: &Program) -> Result<(), ImmediateParsingError> {
    for (i, instruction) in program.instructions.iter().enumerate() {
        for operand in &instruction.sources {
            if let Operand::Immediate(immediate) = operand {
                if match immediate.typ {
                    Type::BaseField => immediate.value.parse::<E::BaseField>().is_err(),
                    Type::Boolean => immediate.value.parse::<bool>().is_err(),
                    Type::Group => immediate.value.parse::<E::BaseField>().is_err(),
                    Type::I8 => immediate.value.parse::<i8>().is_err(),
                    Type::I16 => immediate.value.parse::<i16>().is_err(),
                    Type::I32 => immediate.value.parse::<i32>().is_err(),
                    Type::I64 => immediate.value.parse::<i64>().is_err(),
                    Type::I128 => immediate.value.parse::<i128>().is_err(),
                    Type::ScalarField => immediate.value.parse::<E::ScalarField>().is_err(),
                    Type::U8 => immediate.value.parse::<u8>().is_err(),
                    Type::U16 => immediate.value.parse::<u16>().is_err(),
                    Type::U32 => immediate.value.parse::<u32>().is_err(),
                    Type::U64 => immediate.value.parse::<u64>().is_err(),
                    Type::U128 => immediate.value.parse::<u128>().is_err(),
                } {
                    // TODO (@pranav) Consider aggregating all errors.
                    return Err(ImmediateParsingError {
                        instruction_id: i,
                        typ: immediate.typ,
                        value: immediate.value.clone(),
                    })?;
                }
            }
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
    fn test_immediates_valid() {
        type E = Circuit;
        let (input, program) = Program::new(
            "u8.r0 := addw.u8 0u8, 1u8;\n\
                   u8.r1 := addw.u8 0u8, 2u8;\n\
                   bool.r0 := eq.u8 u8.r0, u8.r1;",
        )
        .unwrap();
        assert!(check_immediates::<E>(&program).is_ok());
    }

    #[test]
    fn test_immediates_invalid() {
        type E = Circuit;
        let (input, program) = Program::new(
            "u8.r0 := addw.u8 0u8, 256u8;\n\
                   u8.r1 := addw.u8 0u8, 2u8;\n\
                   bool.r0 := eq.u8 u8.r0, u8.r1;",
        )
        .unwrap();
        assert!(check_immediates::<E>(&program).is_err());
    }
}
