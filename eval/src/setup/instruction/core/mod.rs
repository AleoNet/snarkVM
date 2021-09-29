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
            bits::TO_BITS_LE_CORE => self.call_core_to_bits_le(arguments),
            bits::FROM_ADDRESS_BITS_LE_CORE => self.call_core_address_from_bits(arguments),
            bits::FROM_BOOL_BITS_LE_CORE => self.call_core_bool_from_bits(arguments),
            bits::FROM_CHAR_BITS_LE_CORE => self.call_core_char_from_bits(arguments),
            bits::FROM_FIELD_BITS_LE_CORE => self.call_core_field_from_bits(arguments),
            bits::FROM_GROUP_BITS_LE_CORE => self.call_core_group_from_bits(arguments),
            bits::FROM_I8_BITS_LE_CORE => self.call_core_i8_from_bits(arguments),
            bits::FROM_I16_BITS_LE_CORE => self.call_core_i16_from_bits(arguments),
            bits::FROM_I32_BITS_LE_CORE => self.call_core_i32_from_bits(arguments),
            bits::FROM_I64_BITS_LE_CORE => self.call_core_i64_from_bits(arguments),
            bits::FROM_I128_BITS_LE_CORE => self.call_core_i128_from_bits(arguments),
            bits::FROM_U8_BITS_LE_CORE => self.call_core_u8_from_bits(arguments),
            bits::FROM_U16_BITS_LE_CORE => self.call_core_u16_from_bits(arguments),
            bits::FROM_U32_BITS_LE_CORE => self.call_core_u32_from_bits(arguments),
            bits::FROM_U64_BITS_LE_CORE => self.call_core_u64_from_bits(arguments),
            bits::FROM_U128_BITS_LE_CORE => self.call_core_u128_from_bits(arguments),
            bytes::TO_BYTES_LE_CORE => self.call_core_to_bytes_le(arguments),
            bytes::FROM_ADDRESS_BYTES_LE_CORE => self.call_core_address_from_bytes(arguments),
            bytes::FROM_BOOL_BYTES_LE_CORE => self.call_core_bool_from_bytes(arguments),
            bytes::FROM_CHAR_BYTES_LE_CORE => self.call_core_char_from_bytes(arguments),
            bytes::FROM_FIELD_BYTES_LE_CORE => self.call_core_field_from_bytes(arguments),
            bytes::FROM_GROUP_BYTES_LE_CORE => self.call_core_group_from_bytes(arguments),
            bytes::FROM_I8_BYTES_LE_CORE => self.call_core_i8_from_bytes(arguments),
            bytes::FROM_I16_BYTES_LE_CORE => self.call_core_i16_from_bytes(arguments),
            bytes::FROM_I32_BYTES_LE_CORE => self.call_core_i32_from_bytes(arguments),
            bytes::FROM_I64_BYTES_LE_CORE => self.call_core_i64_from_bytes(arguments),
            bytes::FROM_I128_BYTES_LE_CORE => self.call_core_i128_from_bytes(arguments),
            bytes::FROM_U8_BYTES_LE_CORE => self.call_core_u8_from_bytes(arguments),
            bytes::FROM_U16_BYTES_LE_CORE => self.call_core_u16_from_bytes(arguments),
            bytes::FROM_U32_BYTES_LE_CORE => self.call_core_u32_from_bytes(arguments),
            bytes::FROM_U64_BYTES_LE_CORE => self.call_core_u64_from_bytes(arguments),
            bytes::FROM_U128_BYTES_LE_CORE => self.call_core_u128_from_bytes(arguments),
            _ => Err(anyhow!("unknown core call: {}", name)),
        }
    }
}
