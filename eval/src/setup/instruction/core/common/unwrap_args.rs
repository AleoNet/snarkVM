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

use crate::{ConstrainedValue, GroupType, Integer};

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{bits::Boolean, integers::uint::UInt8};

use anyhow::*;

macro_rules! unwrap_constrained_array {
    ($function_name:ident, $return_type:ty, $call:expr) => {
        pub fn $function_name<F: PrimeField, G: GroupType<F>>(
            arg: &ConstrainedValue<F, G>,
            expected_len: usize,
            fn_call: &str,
        ) -> Result<Vec<$return_type>> {
            if let ConstrainedValue::Array(args) = arg {
                if args.len() != expected_len {
                    return Err(anyhow!(
                        "illegal `{}` parameter length, expected `{}`",
                        fn_call,
                        expected_len
                    ));
                }

                args.into_iter()
                    .map(|item| $call(item, fn_call))
                    .collect::<Result<Vec<_>>>()
            } else {
                Err(anyhow!("illegal non-array type in `{}` call", fn_call))
            }
        }
    };
}

unwrap_constrained_array!(unwrap_boolean_array_argument, Boolean, |item: &ConstrainedValue<
    F,
    G,
>,
                                                                   fn_call: &str|
 -> Result<Boolean> {
    if let ConstrainedValue::Boolean(boolean) = item {
        Ok(boolean.clone())
    } else {
        Err(anyhow!("illegal non-boolean type in `{}` call", fn_call))
    }
});

unwrap_constrained_array!(unwrap_u8_array_argument, UInt8, |item: &ConstrainedValue<F, G>,
                                                            fn_call: &str|
 -> Result<UInt8> {
    if let ConstrainedValue::Integer(Integer::U8(u8int)) = item {
        Ok(u8int.clone())
    } else {
        Err(anyhow!("illegal non-boolean type in `{}` call", fn_call))
    }
});
