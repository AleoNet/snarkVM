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

use crate::{Program, Type};

// TODO (@pranav) Clean up implementation. Currently a rough prototype.
pub fn check_sequential_ssa(program: Program) {
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


    for instruction in program.instructions {
        for register in instruction.destinations {
            match register.typ {
                Type::BaseField => {
                    if next_base_field_register == register.id {
                        next_base_field_register += 1;
                    } else {
                        panic!("Non-sequential SSA for BaseField");
                    }
                }
                Type::Boolean => {
                    if next_boolean_register == register.id {
                        next_boolean_register += 1;
                    } else {
                        panic!("Non-sequential SSA for Boolean");
                    }
                }
                Type::Group => {
                    if next_group_register == register.id {
                        next_group_register += 1;
                    } else {
                        panic!("Non-sequential SSA for Group");
                    }
                }
                Type::I8 => {
                    if next_i8_register == register.id {
                        next_i8_register += 1;
                    } else {
                        panic!("Non-sequential SSA for I8");
                    }
                }
                Type::I16 => {
                    if next_i16_register == register.id {
                        next_i16_register += 1;
                    } else {
                        panic!("Non-sequential SSA for I16");
                    }
                }
                Type::I32 => {
                    if next_i32_register == register.id {
                        next_i32_register += 1;
                    } else {
                        panic!("Non-sequential SSA for I32");
                    }
                }
                Type::I64 => {
                    if next_i64_register == register.id {
                        next_i64_register += 1;
                    } else {
                        panic!("Non-sequential SSA for I64");
                    }
                }
                Type::I128 => {
                    if next_i128_register == register.id {
                        next_i128_register += 1;
                    } else {
                        panic!("Non-sequential SSA for I128");
                    }
                }
                Type::ScalarField => {
                    if next_scalar_field_register == register.id {
                        next_scalar_field_register += 1;
                    } else {
                        panic!("Non-sequential SSA for ScalarField");
                    }
                }
                Type::U8 => {
                    if next_u8_register == register.id {
                        next_u8_register += 1;
                    } else {
                        panic!("Non-sequential SSA for U8");
                    }
                }
                Type::U16 => {
                    if next_u16_register == register.id {
                        next_u16_register += 1;
                    } else {
                        panic!("Non-sequential SSA for U16");
                    }
                }
                Type::U32 => {
                    if next_u32_register == register.id {
                        next_u32_register += 1;
                    } else {
                        panic!("Non-sequential SSA for U32");
                    }
                }
                Type::U64 => {
                    if next_u64_register == register.id {
                        next_u64_register += 1;
                    } else {
                        panic!("Non-sequential SSA for U64");
                    }
                }
                Type::U128 => {
                    if next_u128_register == register.id {
                        next_u128_register += 1;
                    } else {
                        panic!("Non-sequential SSA for U128");
                    }
                }
            }
        }
    }
}
