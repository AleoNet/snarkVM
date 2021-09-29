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
use snarkvm_gadgets::integers::{int::*, uint::*};

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

pub const FROM_ADDRESS_BITS_LE_CORE: &str = "address_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_address_from_bits(
        &mut self,
        _arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        /* let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, "from_bits")?; */

        Err(anyhow!("the type `address` does not implement the from_bits method"))
    }
}

pub const FROM_BOOL_BITS_LE_CORE: &str = "bool_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_bool_from_bits(
        &mut self,
        _arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        /* let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, "from_bits")?; */

        Err(anyhow!("the type `bool` does not implement the from_bits method"))
    }
}

pub const FROM_CHAR_BITS_LE_CORE: &str = "char_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_char_from_bits(
        &mut self,
        _arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        /* let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, "from_bits")?; */

        Err(anyhow!("the type `char` does not implement the from_bits method"))
    }
}

pub const FROM_FIELD_BITS_LE_CORE: &str = "field_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_field_from_bits(
        &mut self,
        _arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        /* let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, "from_bits")?; */

        Err(anyhow!("the type `field` does not implement the from_bits method"))
    }
}

pub const FROM_GROUP_BITS_LE_CORE: &str = "group_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_group_from_bits(
        &mut self,
        _arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        /* let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, "from_bits")?; */

        Err(anyhow!("the type `group` does not implement the from_bits method"))
    }
}

pub const FROM_I8_BITS_LE_CORE: &str = "i8_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_i8_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 8, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::I8(Int8::from_bits_le(&bits))))
    }
}

pub const FROM_I16_BITS_LE_CORE: &str = "i16_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_i16_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 16, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::I16(Int16::from_bits_le(&bits))))
    }
}
pub const FROM_I32_BITS_LE_CORE: &str = "i32_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_i32_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 32, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::I32(Int32::from_bits_le(&bits))))
    }
}

pub const FROM_I64_BITS_LE_CORE: &str = "i64_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_i64_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 64, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::I64(Int64::from_bits_le(&bits))))
    }
}

pub const FROM_I128_BITS_LE_CORE: &str = "i128_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_i128_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 128, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::I128(Int128::from_bits_le(&bits))))
    }
}

pub const FROM_U8_BITS_LE_CORE: &str = "u8_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_u8_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 8, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::U8(UInt8::from_bits_le(&bits))))
    }
}

pub const FROM_U16_BITS_LE_CORE: &str = "u16_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_u16_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 16, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::U16(UInt16::from_bits_le(&bits))))
    }
}

pub const FROM_U32_BITS_LE_CORE: &str = "u32_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_u32_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 32, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::U32(UInt32::from_bits_le(&bits))))
    }
}

pub const FROM_U64_BITS_LE_CORE: &str = "u64_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_u64_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 64, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::U64(UInt64::from_bits_le(&bits))))
    }
}

pub const FROM_U128_BITS_LE_CORE: &str = "u128_from_bits";
impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_u128_from_bits(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        let arg = match arguments.get(0) {
            None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
            Some(value) => Ok(value),
        }?;
        let bits = unwrap_boolean_array_argument(arg, 128, "from_bits")?;

        Ok(ConstrainedValue::Integer(Integer::U128(UInt128::from_bits_le(&bits))))
    }
}
