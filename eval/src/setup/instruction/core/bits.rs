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

pub const TO_BITS_CORE: &str = "to_bits";

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_to_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let bits = match arguments.get(0) {
            None => Err(anyhow!("illegal `to_bits` call, expected call on target")),
            Some(value) => value.to_bits_le(),
        }?;

        Ok(ConstrainedValue::Array(
            bits.into_iter().map(ConstrainedValue::Boolean).collect(),
        ))
    }
}

pub const FROM_BITS_CORE: &str = "from_bits";

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg);

        ConstrainedValue::from_bits_le(&bits)
    }
}
