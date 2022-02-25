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

use crate::{Operand, Program, Type};

use snarkvm_circuits::{Boolean, Environment};

// TODO (@pranav) Clean up implementation. Currently a rough prototype.
//  - if-let vs match
//  - Error handling
pub fn check_immediates<E: Environment>(program: Program) {
    for instruction in program.instructions {
        for operand in instruction.sources {
            if let Operand::Immediate(immediate) = operand {
                match immediate.typ {
                    Type::BaseField => assert!(immediate.value.parse::<E::BaseField>().is_ok()),
                    Type::Boolean => assert!(immediate.value.parse::<bool>().is_ok()),
                    Type::Group => assert!(immediate.value.parse::<E::BaseField>().is_ok()),
                    Type::I8 => assert!(immediate.value.parse::<i8>().is_ok()),
                    Type::I16 => assert!(immediate.value.parse::<i16>().is_ok()),
                    Type::I32 => assert!(immediate.value.parse::<i32>().is_ok()),
                    Type::I64 => assert!(immediate.value.parse::<i64>().is_ok()),
                    Type::I128 => assert!(immediate.value.parse::<i128>().is_ok()),
                    Type::ScalarField => assert!(immediate.value.parse::<E::ScalarField>().is_ok()),
                    Type::U8 => assert!(immediate.value.parse::<u8>().is_ok()),
                    Type::U16 => assert!(immediate.value.parse::<u16>().is_ok()),
                    Type::U32 => assert!(immediate.value.parse::<u32>().is_ok()),
                    Type::U64 => assert!(immediate.value.parse::<u64>().is_ok()),
                    Type::U128 => assert!(immediate.value.parse::<u128>().is_ok()),
                }
            }
        }
    }
}
