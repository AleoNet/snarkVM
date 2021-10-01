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

use super::*;
use crate::{SimpleInt, SimpleType};

pub const TO_BYTES_LE_CORE: &str = "to_bytes_le";

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_to_bytes_le(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let bytes = match arguments.get(0) {
            None => Err(anyhow!("illegal `to_bytes_le` call, expected call on target")),
            Some(value) => value.to_bytes_le(),
        }?;

        Ok(ConstrainedValue::Array(
            bytes
                .into_iter()
                .map(Integer::U8)
                .map(ConstrainedValue::Integer)
                .collect(),
        ))
    }
}

pub const FROM_BYTES_LE_CORE: &str = "_from_bytes_le";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_from_bytes_le(
        &mut self,
        call: &str,
        arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bytes` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;

        let (type_, num_of_expected_bytes) = match call {
            // TODO update non integer types with correct number of
            // bits in future when known.
            "address_from_bytes_le" => (SimpleType::Address, 8),
            "bool_from_bytes_le" => (SimpleType::Boolean, 8),
            "char_from_bytes_le" => (SimpleType::Char, 8),
            "field_from_bytes_le" => (SimpleType::Field, 8),
            "group_from_bytes_le" => (SimpleType::Group, 8),
            "i8_from_bytes_le" => (SimpleType::Integer(SimpleInt::I8), 1),
            "i16_from_bytes_le" => (SimpleType::Integer(SimpleInt::I16), 2),
            "i32_from_bytes_le" => (SimpleType::Integer(SimpleInt::I32), 4),
            "i64_from_bytes_le" => (SimpleType::Integer(SimpleInt::I64), 8),
            "i128_from_bytes_le" => (SimpleType::Integer(SimpleInt::I128), 16),
            "u8_from_bytes_le" => (SimpleType::Integer(SimpleInt::U8), 1),
            "u16_from_bytes_le" => (SimpleType::Integer(SimpleInt::U16), 2),
            "u32_from_bytes_le" => (SimpleType::Integer(SimpleInt::U32), 4),
            "u64_from_bytes_le" => (SimpleType::Integer(SimpleInt::U64), 8),
            "u128_from_bytes_le" => (SimpleType::Integer(SimpleInt::U128), 16),
            _ => return Err(anyhow!("the type `unknown` does not implement the from_bits_le method")),
        };

        let bytes = unwrap_u8_array_argument(arg, num_of_expected_bytes, "from_bytes")?;

        ConstrainedValue::from_bytes_le(type_, &bytes)
    }
}
