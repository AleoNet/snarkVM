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
use snarkvm_gadgets::{
    integers::{int::*, uint::*},
    FromBitsLEGadget,
    ToBitsBEGadget,
    ToBitsLEGadget,
};

// This macro can be more efficient once concat_idents is merged in.
macro_rules! to_bits_impl {
    ($le_function_name:ident, $be_function_name:ident, $le_constant_name:ident, $le_constant_value:literal, $be_constant_name:ident, $be_constant_value:literal) => {
        pub const $le_constant_name: &str = $le_constant_value;

        impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
            pub fn $le_function_name(
                &mut self,
                arguments: &[ConstrainedValue<F, G>],
            ) -> Result<ConstrainedValue<F, G>> {
                let cs = self.cs();

                let bits = match arguments.get(0) {
                    None => Err(anyhow!("illegal `to_bits_le` call, expected call on target")),
                    Some(value) => value.to_bits_le(cs).map_err(|e| anyhow!(e)),
                }?;

                Ok(ConstrainedValue::Array(
                    bits.into_iter().map(ConstrainedValue::Boolean).collect(),
                ))
            }
        }

        pub const $be_constant_name: &str = $be_constant_value;

        impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
            pub fn $be_function_name(
                &mut self,
                arguments: &[ConstrainedValue<F, G>],
            ) -> Result<ConstrainedValue<F, G>> {
                let cs = self.cs();

                let bits = match arguments.get(0) {
                    None => Err(anyhow!("illegal `to_bits_le` call, expected call on target")),
                    Some(value) => (*value).to_bits_be(cs).map_err(|e| anyhow!(e)),
                }?;

                Ok(ConstrainedValue::Array(
                    bits.into_iter().map(ConstrainedValue::Boolean).collect(),
                ))
            }
        }
    };
}

to_bits_impl!(
    call_core_address_to_bits_le,
    call_core_address_to_bits_be,
    ADDRESS_TO_BITS_LE_CORE,
    "address_to_bits_le",
    ADDRESS_TO_BITS_BE_CORE,
    "address_to_bits_be"
);
to_bits_impl!(
    call_core_bool_to_bits_le,
    call_core_bool_to_bits_be,
    BOOL_TO_BITS_LE_CORE,
    "bool_to_bits_le",
    BOOL_TO_BITS_BE_CORE,
    "bool_to_bits_be"
);
to_bits_impl!(
    call_core_char_to_bits_le,
    call_core_char_to_bits_be,
    CHAR_TO_BITS_LE_CORE,
    "char_to_bits_le",
    CHAR_TO_BITS_BE_CORE,
    "char_to_bits_be"
);
to_bits_impl!(
    call_core_field_to_bits_le,
    call_core_field_to_bits_be,
    FIELD_TO_BITS_LE_CORE,
    "field_to_bits_le",
    FIELD_TO_BITS_BE_CORE,
    "field_to_bits_be"
);
to_bits_impl!(
    call_core_group_to_bits_le,
    call_core_group_to_bits_be,
    GROUP_TO_BITS_LE_CORE,
    "group_to_bits_le",
    GROUP_TO_BITS_BE_CORE,
    "group_to_bits_be"
);
to_bits_impl!(
    call_core_i8_to_bits_le,
    call_core_i8_to_bits_be,
    I8_TO_BITS_LE_CORE,
    "i8_to_bits_le",
    I8_TO_BITS_BE_CORE,
    "i8_to_bits_be"
);
to_bits_impl!(
    call_core_i16_to_bits_le,
    call_core_i16_to_bits_be,
    I16_TO_BITS_LE_CORE,
    "i16_to_bits_le",
    I16_TO_BITS_BE_CORE,
    "i16_to_bits_be"
);
to_bits_impl!(
    call_core_i32_to_bits_le,
    call_core_i32_to_bits_be,
    I32_TO_BITS_LE_CORE,
    "i32_to_bits_le",
    I32_TO_BITS_BE_CORE,
    "i32_to_bits_be"
);
to_bits_impl!(
    call_core_i64_to_bits_le,
    call_core_i64_to_bits_be,
    I64_TO_BITS_LE_CORE,
    "i64_to_bits_le",
    I64_TO_BITS_BE_CORE,
    "i64_to_bits_be"
);
to_bits_impl!(
    call_core_i128_to_bits_le,
    call_core_i128_to_bits_be,
    I128_TO_BITS_LE_CORE,
    "i128_to_bits_le",
    I128_TO_BITS_BE_CORE,
    "i128_to_bits_be"
);
to_bits_impl!(
    call_core_u8_to_bits_le,
    call_core_u8_to_bits_be,
    U8_TO_BITS_LE_CORE,
    "u8_to_bits_le",
    U8_TO_BITS_BE_CORE,
    "u8_to_bits_be"
);
to_bits_impl!(
    call_core_u16_to_bits_le,
    call_core_u16_to_bits_be,
    U16_TO_BITS_LE_CORE,
    "u16_to_bits_le",
    U16_TO_BITS_BE_CORE,
    "u16_to_bits_be"
);
to_bits_impl!(
    call_core_u32_to_bits_le,
    call_core_u32_to_bits_be,
    U32_TO_BITS_LE_CORE,
    "u32_to_bits_le",
    U32_TO_BITS_BE_CORE,
    "u32_to_bits_be"
);
to_bits_impl!(
    call_core_u64_to_bits_le,
    call_core_u64_to_bits_be,
    U64_TO_BITS_LE_CORE,
    "u64_to_bits_le",
    U64_TO_BITS_BE_CORE,
    "u64_to_bits_be"
);
to_bits_impl!(
    call_core_u128_to_bits_le,
    call_core_u128_to_bits_be,
    U128_TO_BITS_LE_CORE,
    "u128_to_bits_le",
    U128_TO_BITS_BE_CORE,
    "u128_to_bits_be"
);

// This macro can be more efficient once concat_idents is merged in.
macro_rules! from_bits_impl {
    ($function_name:ident, $constant_name:ident, $constant_value:literal, $num_of_expected_bits:literal, $call:expr) => {
        pub const $constant_name: &str = $constant_value;

        impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
            pub fn $function_name(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
                let arg = match arguments.get(0) {
                    None => Err(anyhow!("illegal `from_bits` call, expected 1 argument")),
                    Some(value) => Ok(value),
                }?;

                let bits = unwrap_boolean_array_argument(arg, $num_of_expected_bits, "from_bits")?;

                $call(&bits)
            }
        }
    };
}

from_bits_impl!(
    call_core_address_from_bits_le,
    ADDRESS_FROM_BITS_LE_CORE,
    "address_from_bits_le",
    8,
    |_bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Err(anyhow!("the type `address` does not implement the from_bits_le method"))
    }
);
from_bits_impl!(
    call_core_bool_from_bits_le,
    BOOL_FROM_BITS_LE_CORE,
    "bool_from_bits_le",
    8,
    |_bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Err(anyhow!("the type `bool` does not implement the from_bits_le method"))
    }
);
from_bits_impl!(
    call_core_char_from_bits_le,
    CHAR_FROM_BITS_LE_CORE,
    "char_from_bits_le",
    8,
    |_bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Err(anyhow!("the type `char` does not implement the from_bits_le method"))
    }
);
from_bits_impl!(
    call_core_field_from_bits_le,
    FIELD_FROM_BITS_LE_CORE,
    "field_from_bits_le",
    8,
    |_bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Err(anyhow!("the type `field` does not implement the from_bits_le method"))
    }
);
from_bits_impl!(
    call_core_group_from_bits_le,
    GROUP_FROM_BITS_LE_CORE,
    "group_from_bits_le",
    8,
    |_bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Err(anyhow!("the type `group` does not implement the from_bits_le method"))
    }
);
from_bits_impl!(
    call_core_i8_from_bits_le,
    I8_FROM_BITS_LE_CORE,
    "i8_from_bits_le",
    8,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::I8(Int8::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_i16_from_bits_le,
    I16_FROM_BITS_LE_CORE,
    "i16_from_bits_le",
    16,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::I16(Int16::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_i32_from_bits_le,
    I32_FROM_BITS_LE_CORE,
    "i32_from_bits_le",
    32,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::I32(Int32::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_i64_from_bits_le,
    I64_FROM_BITS_LE_CORE,
    "i64_from_bits_le",
    64,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::I64(Int64::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_i128_from_bits_le,
    I128_FROM_BITS_LE_CORE,
    "i128_from_bits_le",
    128,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::I128(Int128::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_u8_from_bits_le,
    U8_FROM_BITS_LE_CORE,
    "u8_from_bits_le",
    8,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::U8(UInt8::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_u16_from_bits_le,
    U16_FROM_BITS_LE_CORE,
    "u16_from_bits_le",
    16,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::U16(UInt16::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_u32_from_bits_le,
    U32_FROM_BITS_LE_CORE,
    "u32_from_bits_le",
    32,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::U32(UInt32::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_u64_from_bits_le,
    U64_FROM_BITS_LE_CORE,
    "u64_from_bits_le",
    64,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::U64(UInt64::from_bits_le(bits)?)))
    }
);
from_bits_impl!(
    call_core_u128_from_bits_le,
    U128_FROM_BITS_LE_CORE,
    "u128_from_bits_le",
    128,
    |bits: &[Boolean]| -> Result<ConstrainedValue<F, G>> {
        Ok(ConstrainedValue::Integer(Integer::U128(UInt128::from_bits_le(bits)?)))
    }
);
