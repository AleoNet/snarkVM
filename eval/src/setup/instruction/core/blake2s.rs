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

use snarkvm_gadgets::{algorithms::prf::Blake2sGadget, PRFGadget, ToBytesLEGadget};

use super::*;

pub const BLAKE2S_HASH_CORE: &str = "hash";

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_blake2s_hash(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        if arguments.len() != 2 {
            return Err(anyhow!("illegal blake2s hash call, expected 2 arguments"));
        }
        let input = unwrap_u8_array_argument(&arguments[1], 32, "hash")?;
        let seed = unwrap_u8_array_argument(&arguments[0], 32, "hash")?;
        let mut cs = self.cs();
        let digest = Blake2sGadget::check_evaluation_gadget(cs.ns(|| "blake2s hash"), &seed[..], &input[..])
            .map_err(|e| ValueError::cannot_enforce("Blake2s check evaluation gadget", e))?;

        Ok(ConstrainedValue::Array(
            digest
                .to_bytes_le(&mut cs)
                .map_err(|e| ValueError::cannot_enforce("Vec<UInt8> ToBytes", e))?
                .into_iter()
                .map(Integer::U8)
                .map(ConstrainedValue::Integer)
                .collect(),
        ))
    }
}
