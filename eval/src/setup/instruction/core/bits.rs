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

pub const TO_BITS_LE_CORE: &str = "to_bits_le";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_to_bits_le(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let bits = match arguments.get(0) {
            None => Err(anyhow!("illegal `to_bits_le` call, expected call on target")),
            Some(value) => value.to_bits_le(),
        }?;

        Ok(ConstrainedValue::Array(
            bits.into_iter().map(ConstrainedValue::Boolean).collect(),
        ))
    }
}

pub const FROM_BITS_LE_CORE: &str = "_from_bits_le";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_from_bits_le(
        &mut self,
        call: &str,
        arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;

        let (type_, num_of_expected_bits) = match call {
            // TODO update non integer types with correct number of
            // bits in future when known.
            "address_from_bits_le" => (SimpleType::Address, 8),
            "bool_from_bits_le" => (SimpleType::Boolean, 8),
            "char_from_bits_le" => (SimpleType::Char, 8),
            "field_from_bits_le" => (SimpleType::Field, 8),
            "group_from_bits_le" => (SimpleType::Group, 8),
            "i8_from_bits_le" => (SimpleType::Integer(SimpleInt::I8), 8),
            "i16_from_bits_le" => (SimpleType::Integer(SimpleInt::I16), 16),
            "i32_from_bits_le" => (SimpleType::Integer(SimpleInt::I32), 32),
            "i64_from_bits_le" => (SimpleType::Integer(SimpleInt::I64), 64),
            "i128_from_bits_le" => (SimpleType::Integer(SimpleInt::I128), 128),
            "u8_from_bits_le" => (SimpleType::Integer(SimpleInt::U8), 8),
            "u16_from_bits_le" => (SimpleType::Integer(SimpleInt::U16), 16),
            "u32_from_bits_le" => (SimpleType::Integer(SimpleInt::U32), 32),
            "u64_from_bits_le" => (SimpleType::Integer(SimpleInt::U64), 64),
            "u128_from_bits_le" => (SimpleType::Integer(SimpleInt::U128), 128),
            _ => return Err(anyhow!("the type `unknown` does not implement the from_bits_le method")),
        };

        let bits = unwrap_boolean_array_argument(arg, num_of_expected_bits, "from_bits")?;

        ConstrainedValue::from_bits_le(type_, &bits)
    }
}
