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

mod blake2s;
pub mod common;
pub use common::*;
mod from_bits;
mod from_bytes;
pub mod len;
pub use len::*;
mod to_bits;
mod to_bytes;

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core(&mut self, name: &str, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        match name {
            blake2s::BLAKE2S_HASH_CORE => self.call_core_blake2s_hash(arguments),
            len::LEN_CORE => self.call_core_len(arguments),
            // to_bits_le
            to_bits::ADDRESS_TO_BITS_LE_CORE => self.call_core_address_to_bits_le(arguments),
            to_bits::BOOL_TO_BITS_LE_CORE => self.call_core_bool_to_bits_le(arguments),
            to_bits::CHAR_TO_BITS_LE_CORE => self.call_core_char_to_bits_le(arguments),
            to_bits::FIELD_TO_BITS_LE_CORE => self.call_core_field_to_bits_le(arguments),
            to_bits::GROUP_TO_BITS_LE_CORE => self.call_core_group_to_bits_le(arguments),
            to_bits::I8_TO_BITS_LE_CORE => self.call_core_i8_to_bits_le(arguments),
            to_bits::I16_TO_BITS_LE_CORE => self.call_core_i16_to_bits_le(arguments),
            to_bits::I32_TO_BITS_LE_CORE => self.call_core_i32_to_bits_le(arguments),
            to_bits::I64_TO_BITS_LE_CORE => self.call_core_i64_to_bits_le(arguments),
            to_bits::I128_TO_BITS_LE_CORE => self.call_core_i128_to_bits_le(arguments),
            to_bits::U8_TO_BITS_LE_CORE => self.call_core_u8_to_bits_le(arguments),
            to_bits::U16_TO_BITS_LE_CORE => self.call_core_u16_to_bits_le(arguments),
            to_bits::U32_TO_BITS_LE_CORE => self.call_core_u32_to_bits_le(arguments),
            to_bits::U64_TO_BITS_LE_CORE => self.call_core_u64_to_bits_le(arguments),
            to_bits::U128_TO_BITS_LE_CORE => self.call_core_u128_to_bits_le(arguments),
            // to_bits_be
            to_bits::ADDRESS_TO_BITS_BE_CORE => self.call_core_address_to_bits_be(arguments),
            to_bits::BOOL_TO_BITS_BE_CORE => self.call_core_bool_to_bits_be(arguments),
            to_bits::CHAR_TO_BITS_BE_CORE => self.call_core_char_to_bits_be(arguments),
            to_bits::FIELD_TO_BITS_BE_CORE => self.call_core_field_to_bits_be(arguments),
            to_bits::GROUP_TO_BITS_BE_CORE => self.call_core_group_to_bits_be(arguments),
            to_bits::I8_TO_BITS_BE_CORE => self.call_core_i8_to_bits_be(arguments),
            to_bits::I16_TO_BITS_BE_CORE => self.call_core_i16_to_bits_be(arguments),
            to_bits::I32_TO_BITS_BE_CORE => self.call_core_i32_to_bits_be(arguments),
            to_bits::I64_TO_BITS_BE_CORE => self.call_core_i64_to_bits_be(arguments),
            to_bits::I128_TO_BITS_BE_CORE => self.call_core_i128_to_bits_be(arguments),
            to_bits::U8_TO_BITS_BE_CORE => self.call_core_u8_to_bits_be(arguments),
            to_bits::U16_TO_BITS_BE_CORE => self.call_core_u16_to_bits_be(arguments),
            to_bits::U32_TO_BITS_BE_CORE => self.call_core_u32_to_bits_be(arguments),
            to_bits::U64_TO_BITS_BE_CORE => self.call_core_u64_to_bits_be(arguments),
            to_bits::U128_TO_BITS_BE_CORE => self.call_core_u128_to_bits_be(arguments),
            // from_bits_le
            from_bits::ADDRESS_FROM_BITS_LE_CORE => self.call_core_address_from_bits_le(arguments),
            from_bits::BOOL_FROM_BITS_LE_CORE => self.call_core_bool_from_bits_le(arguments),
            from_bits::CHAR_FROM_BITS_LE_CORE => self.call_core_char_from_bits_le(arguments),
            from_bits::FIELD_FROM_BITS_LE_CORE => self.call_core_field_from_bits_le(arguments),
            from_bits::GROUP_FROM_BITS_LE_CORE => self.call_core_group_from_bits_le(arguments),
            from_bits::I8_FROM_BITS_LE_CORE => self.call_core_i8_from_bits_le(arguments),
            from_bits::I16_FROM_BITS_LE_CORE => self.call_core_i16_from_bits_le(arguments),
            from_bits::I32_FROM_BITS_LE_CORE => self.call_core_i32_from_bits_le(arguments),
            from_bits::I64_FROM_BITS_LE_CORE => self.call_core_i64_from_bits_le(arguments),
            from_bits::I128_FROM_BITS_LE_CORE => self.call_core_i128_from_bits_le(arguments),
            from_bits::U8_FROM_BITS_LE_CORE => self.call_core_u8_from_bits_le(arguments),
            from_bits::U16_FROM_BITS_LE_CORE => self.call_core_u16_from_bits_le(arguments),
            from_bits::U32_FROM_BITS_LE_CORE => self.call_core_u32_from_bits_le(arguments),
            from_bits::U64_FROM_BITS_LE_CORE => self.call_core_u64_from_bits_le(arguments),
            from_bits::U128_FROM_BITS_LE_CORE => self.call_core_u128_from_bits_le(arguments),
            // from_bits_be
            from_bits::ADDRESS_FROM_BITS_BE_CORE => self.call_core_address_from_bits_be(arguments),
            from_bits::BOOL_FROM_BITS_BE_CORE => self.call_core_bool_from_bits_be(arguments),
            from_bits::CHAR_FROM_BITS_BE_CORE => self.call_core_char_from_bits_be(arguments),
            from_bits::FIELD_FROM_BITS_BE_CORE => self.call_core_field_from_bits_be(arguments),
            from_bits::GROUP_FROM_BITS_BE_CORE => self.call_core_group_from_bits_be(arguments),
            from_bits::I8_FROM_BITS_BE_CORE => self.call_core_i8_from_bits_be(arguments),
            from_bits::I16_FROM_BITS_BE_CORE => self.call_core_i16_from_bits_be(arguments),
            from_bits::I32_FROM_BITS_BE_CORE => self.call_core_i32_from_bits_be(arguments),
            from_bits::I64_FROM_BITS_BE_CORE => self.call_core_i64_from_bits_be(arguments),
            from_bits::I128_FROM_BITS_BE_CORE => self.call_core_i128_from_bits_be(arguments),
            from_bits::U8_FROM_BITS_BE_CORE => self.call_core_u8_from_bits_be(arguments),
            from_bits::U16_FROM_BITS_BE_CORE => self.call_core_u16_from_bits_be(arguments),
            from_bits::U32_FROM_BITS_BE_CORE => self.call_core_u32_from_bits_be(arguments),
            from_bits::U64_FROM_BITS_BE_CORE => self.call_core_u64_from_bits_be(arguments),
            from_bits::U128_FROM_BITS_BE_CORE => self.call_core_u128_from_bits_be(arguments),
            // to_bytes_le
            to_bytes::ADDRESS_TO_BYTES_LE_CORE => self.call_core_address_to_bytes_le(arguments),
            to_bytes::BOOL_TO_BYTES_LE_CORE => self.call_core_bool_to_bytes_le(arguments),
            to_bytes::CHAR_TO_BYTES_LE_CORE => self.call_core_char_to_bytes_le(arguments),
            to_bytes::FIELD_TO_BYTES_LE_CORE => self.call_core_field_to_bytes_le(arguments),
            to_bytes::GROUP_TO_BYTES_LE_CORE => self.call_core_group_to_bytes_le(arguments),
            to_bytes::I8_TO_BYTES_LE_CORE => self.call_core_i8_to_bytes_le(arguments),
            to_bytes::I16_TO_BYTES_LE_CORE => self.call_core_i16_to_bytes_le(arguments),
            to_bytes::I32_TO_BYTES_LE_CORE => self.call_core_i32_to_bytes_le(arguments),
            to_bytes::I64_TO_BYTES_LE_CORE => self.call_core_i64_to_bytes_le(arguments),
            to_bytes::I128_TO_BYTES_LE_CORE => self.call_core_i128_to_bytes_le(arguments),
            to_bytes::U8_TO_BYTES_LE_CORE => self.call_core_u8_to_bytes_le(arguments),
            to_bytes::U16_TO_BYTES_LE_CORE => self.call_core_u16_to_bytes_le(arguments),
            to_bytes::U32_TO_BYTES_LE_CORE => self.call_core_u32_to_bytes_le(arguments),
            to_bytes::U64_TO_BYTES_LE_CORE => self.call_core_u64_to_bytes_le(arguments),
            to_bytes::U128_TO_BYTES_LE_CORE => self.call_core_u128_to_bytes_le(arguments),
            // to_bytes_be
            to_bytes::ADDRESS_TO_BYTES_BE_CORE => self.call_core_address_to_bytes_be(arguments),
            to_bytes::BOOL_TO_BYTES_BE_CORE => self.call_core_bool_to_bytes_be(arguments),
            to_bytes::CHAR_TO_BYTES_BE_CORE => self.call_core_char_to_bytes_be(arguments),
            to_bytes::FIELD_TO_BYTES_BE_CORE => self.call_core_field_to_bytes_be(arguments),
            to_bytes::GROUP_TO_BYTES_BE_CORE => self.call_core_group_to_bytes_be(arguments),
            to_bytes::I8_TO_BYTES_BE_CORE => self.call_core_i8_to_bytes_be(arguments),
            to_bytes::I16_TO_BYTES_BE_CORE => self.call_core_i16_to_bytes_be(arguments),
            to_bytes::I32_TO_BYTES_BE_CORE => self.call_core_i32_to_bytes_be(arguments),
            to_bytes::I64_TO_BYTES_BE_CORE => self.call_core_i64_to_bytes_be(arguments),
            to_bytes::I128_TO_BYTES_BE_CORE => self.call_core_i128_to_bytes_be(arguments),
            to_bytes::U8_TO_BYTES_BE_CORE => self.call_core_u8_to_bytes_be(arguments),
            to_bytes::U16_TO_BYTES_BE_CORE => self.call_core_u16_to_bytes_be(arguments),
            to_bytes::U32_TO_BYTES_BE_CORE => self.call_core_u32_to_bytes_be(arguments),
            to_bytes::U64_TO_BYTES_BE_CORE => self.call_core_u64_to_bytes_be(arguments),
            to_bytes::U128_TO_BYTES_BE_CORE => self.call_core_u128_to_bytes_be(arguments),
            // from_bytes_le
            from_bytes::ADDRESS_FROM_BYTES_LE_CORE => self.call_core_address_from_bytes_le(arguments),
            from_bytes::BOOL_FROM_BYTES_LE_CORE => self.call_core_bool_from_bytes_le(arguments),
            from_bytes::CHAR_FROM_BYTES_LE_CORE => self.call_core_char_from_bytes_le(arguments),
            from_bytes::FIELD_FROM_BYTES_LE_CORE => self.call_core_field_from_bytes_le(arguments),
            from_bytes::GROUP_FROM_BYTES_LE_CORE => self.call_core_group_from_bytes_le(arguments),
            from_bytes::I8_FROM_BYTES_LE_CORE => self.call_core_i8_from_bytes_le(arguments),
            from_bytes::I16_FROM_BYTES_LE_CORE => self.call_core_i16_from_bytes_le(arguments),
            from_bytes::I32_FROM_BYTES_LE_CORE => self.call_core_i32_from_bytes_le(arguments),
            from_bytes::I64_FROM_BYTES_LE_CORE => self.call_core_i64_from_bytes_le(arguments),
            from_bytes::I128_FROM_BYTES_LE_CORE => self.call_core_i128_from_bytes_le(arguments),
            from_bytes::U8_FROM_BYTES_LE_CORE => self.call_core_u8_from_bytes_le(arguments),
            from_bytes::U16_FROM_BYTES_LE_CORE => self.call_core_u16_from_bytes_le(arguments),
            from_bytes::U32_FROM_BYTES_LE_CORE => self.call_core_u32_from_bytes_le(arguments),
            from_bytes::U64_FROM_BYTES_LE_CORE => self.call_core_u64_from_bytes_le(arguments),
            from_bytes::U128_FROM_BYTES_LE_CORE => self.call_core_u128_from_bytes_le(arguments),
            // from_bytes_be
            from_bytes::ADDRESS_FROM_BYTES_BE_CORE => self.call_core_address_from_bytes_be(arguments),
            from_bytes::BOOL_FROM_BYTES_BE_CORE => self.call_core_bool_from_bytes_be(arguments),
            from_bytes::CHAR_FROM_BYTES_BE_CORE => self.call_core_char_from_bytes_be(arguments),
            from_bytes::FIELD_FROM_BYTES_BE_CORE => self.call_core_field_from_bytes_be(arguments),
            from_bytes::GROUP_FROM_BYTES_BE_CORE => self.call_core_group_from_bytes_be(arguments),
            from_bytes::I8_FROM_BYTES_BE_CORE => self.call_core_i8_from_bytes_be(arguments),
            from_bytes::I16_FROM_BYTES_BE_CORE => self.call_core_i16_from_bytes_be(arguments),
            from_bytes::I32_FROM_BYTES_BE_CORE => self.call_core_i32_from_bytes_be(arguments),
            from_bytes::I64_FROM_BYTES_BE_CORE => self.call_core_i64_from_bytes_be(arguments),
            from_bytes::I128_FROM_BYTES_BE_CORE => self.call_core_i128_from_bytes_be(arguments),
            from_bytes::U8_FROM_BYTES_BE_CORE => self.call_core_u8_from_bytes_be(arguments),
            from_bytes::U16_FROM_BYTES_BE_CORE => self.call_core_u16_from_bytes_be(arguments),
            from_bytes::U32_FROM_BYTES_BE_CORE => self.call_core_u32_from_bytes_be(arguments),
            from_bytes::U64_FROM_BYTES_BE_CORE => self.call_core_u64_from_bytes_be(arguments),
            from_bytes::U128_FROM_BYTES_BE_CORE => self.call_core_u128_from_bytes_be(arguments),
            _ => Err(anyhow!("unknown core call: {}", name)),
        }
    }
}
