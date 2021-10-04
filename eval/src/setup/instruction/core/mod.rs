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

mod bits;
mod blake2s;
mod bytes;
pub mod common;
pub use common::*;
pub mod len;
pub use len::*;

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core(&mut self, name: &str, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        match name {
            blake2s::BLAKE2S_HASH_CORE => self.call_core_blake2s_hash(arguments),
            len::LEN_CORE => self.call_core_len(arguments),
            // to_bits_le
            bits::ADDRESS_TO_BITS_LE_CORE => self.call_core_address_to_bits_le(arguments),
            bits::BOOL_TO_BITS_LE_CORE => self.call_core_bool_to_bits_le(arguments),
            bits::CHAR_TO_BITS_LE_CORE => self.call_core_char_to_bits_le(arguments),
            bits::FIELD_TO_BITS_LE_CORE => self.call_core_field_to_bits_le(arguments),
            bits::GROUP_TO_BITS_LE_CORE => self.call_core_group_to_bits_le(arguments),
            bits::I8_TO_BITS_LE_CORE => self.call_core_i8_to_bits_le(arguments),
            bits::I16_TO_BITS_LE_CORE => self.call_core_i16_to_bits_le(arguments),
            bits::I32_TO_BITS_LE_CORE => self.call_core_i32_to_bits_le(arguments),
            bits::I64_TO_BITS_LE_CORE => self.call_core_i64_to_bits_le(arguments),
            bits::I128_TO_BITS_LE_CORE => self.call_core_i128_to_bits_le(arguments),
            bits::U8_TO_BITS_LE_CORE => self.call_core_u8_to_bits_le(arguments),
            bits::U16_TO_BITS_LE_CORE => self.call_core_u16_to_bits_le(arguments),
            bits::U32_TO_BITS_LE_CORE => self.call_core_u32_to_bits_le(arguments),
            bits::U64_TO_BITS_LE_CORE => self.call_core_u64_to_bits_le(arguments),
            bits::U128_TO_BITS_LE_CORE => self.call_core_u128_to_bits_le(arguments),
            // from_bits_le
            bits::ADDRESS_FROM_BITS_LE_CORE => self.call_core_address_from_bits_le(arguments),
            bits::BOOL_FROM_BITS_LE_CORE => self.call_core_bool_from_bits_le(arguments),
            bits::CHAR_FROM_BITS_LE_CORE => self.call_core_char_from_bits_le(arguments),
            bits::FIELD_FROM_BITS_LE_CORE => self.call_core_field_from_bits_le(arguments),
            bits::GROUP_FROM_BITS_LE_CORE => self.call_core_group_from_bits_le(arguments),
            bits::I8_FROM_BITS_LE_CORE => self.call_core_i8_from_bits_le(arguments),
            bits::I16_FROM_BITS_LE_CORE => self.call_core_i16_from_bits_le(arguments),
            bits::I32_FROM_BITS_LE_CORE => self.call_core_i32_from_bits_le(arguments),
            bits::I64_FROM_BITS_LE_CORE => self.call_core_i64_from_bits_le(arguments),
            bits::I128_FROM_BITS_LE_CORE => self.call_core_i128_from_bits_le(arguments),
            bits::U8_FROM_BITS_LE_CORE => self.call_core_u8_from_bits_le(arguments),
            bits::U16_FROM_BITS_LE_CORE => self.call_core_u16_from_bits_le(arguments),
            bits::U32_FROM_BITS_LE_CORE => self.call_core_u32_from_bits_le(arguments),
            bits::U64_FROM_BITS_LE_CORE => self.call_core_u64_from_bits_le(arguments),
            bits::U128_FROM_BITS_LE_CORE => self.call_core_u128_from_bits_le(arguments),
            // to_bytes_le
            bytes::ADDRESS_TO_BYTES_LE_CORE => self.call_core_address_to_bytes_le(arguments),
            bytes::BOOL_TO_BYTES_LE_CORE => self.call_core_bool_to_bytes_le(arguments),
            bytes::CHAR_TO_BYTES_LE_CORE => self.call_core_char_to_bytes_le(arguments),
            bytes::FIELD_TO_BYTES_LE_CORE => self.call_core_field_to_bytes_le(arguments),
            bytes::GROUP_TO_BYTES_LE_CORE => self.call_core_group_to_bytes_le(arguments),
            bytes::I8_TO_BYTES_LE_CORE => self.call_core_i8_to_bytes_le(arguments),
            bytes::I16_TO_BYTES_LE_CORE => self.call_core_i16_to_bytes_le(arguments),
            bytes::I32_TO_BYTES_LE_CORE => self.call_core_i32_to_bytes_le(arguments),
            bytes::I64_TO_BYTES_LE_CORE => self.call_core_i64_to_bytes_le(arguments),
            bytes::I128_TO_BYTES_LE_CORE => self.call_core_i128_to_bytes_le(arguments),
            bytes::U8_TO_BYTES_LE_CORE => self.call_core_u8_to_bytes_le(arguments),
            bytes::U16_TO_BYTES_LE_CORE => self.call_core_u16_to_bytes_le(arguments),
            bytes::U32_TO_BYTES_LE_CORE => self.call_core_u32_to_bytes_le(arguments),
            bytes::U64_TO_BYTES_LE_CORE => self.call_core_u64_to_bytes_le(arguments),
            bytes::U128_TO_BYTES_LE_CORE => self.call_core_u128_to_bytes_le(arguments),
            // from_bytes_le
            bytes::ADDRESS_FROM_BYTES_LE_CORE => self.call_core_address_from_bytes_le(arguments),
            bytes::BOOL_FROM_BYTES_LE_CORE => self.call_core_bool_from_bytes_le(arguments),
            bytes::CHAR_FROM_BYTES_LE_CORE => self.call_core_char_from_bytes_le(arguments),
            bytes::FIELD_FROM_BYTES_LE_CORE => self.call_core_field_from_bytes_le(arguments),
            bytes::GROUP_FROM_BYTES_LE_CORE => self.call_core_group_from_bytes_le(arguments),
            bytes::I8_FROM_BYTES_LE_CORE => self.call_core_i8_from_bytes_le(arguments),
            bytes::I16_FROM_BYTES_LE_CORE => self.call_core_i16_from_bytes_le(arguments),
            bytes::I32_FROM_BYTES_LE_CORE => self.call_core_i32_from_bytes_le(arguments),
            bytes::I64_FROM_BYTES_LE_CORE => self.call_core_i64_from_bytes_le(arguments),
            bytes::I128_FROM_BYTES_LE_CORE => self.call_core_i128_from_bytes_le(arguments),
            bytes::U8_FROM_BYTES_LE_CORE => self.call_core_u8_from_bytes_le(arguments),
            bytes::U16_FROM_BYTES_LE_CORE => self.call_core_u16_from_bytes_le(arguments),
            bytes::U32_FROM_BYTES_LE_CORE => self.call_core_u32_from_bytes_le(arguments),
            bytes::U64_FROM_BYTES_LE_CORE => self.call_core_u64_from_bytes_le(arguments),
            bytes::U128_FROM_BYTES_LE_CORE => self.call_core_u128_from_bytes_le(arguments),
            _ => Err(anyhow!("unknown core call: {}", name)),
        }
    }
}
