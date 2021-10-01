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
            from_bits if name.ends_with(bits::FROM_BITS_LE_CORE) => self.call_core_from_bits_le(from_bits, arguments),
            bytes::TO_BYTES_LE_CORE => self.call_core_to_bytes_le(arguments),
            from_bytes if name.ends_with(bytes::FROM_BYTES_LE_CORE) => {
                self.call_core_from_bytes_le(from_bytes, arguments)
            }
            _ => Err(anyhow!("unknown core call: {}", name)),
        }
    }
}
