// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use core::borrow::Borrow;

use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::boolean::{AllocatedBit, Boolean},
    integers::uint::*,
    traits::{alloc::AllocGadget, integers::Integer},
};

macro_rules! alloc_gadget_fn_impl {
    ($gadget: ident, $fn_name: ident) => {
        fn $fn_name<
            Fn: FnOnce() -> Result<T, SynthesisError>,
            T: Borrow<<$gadget as Integer>::IntegerType>,
            CS: ConstraintSystem<F>,
        >(
            mut cs: CS,
            value_gen: Fn,
        ) -> Result<Self, SynthesisError> {
            if cs.is_in_setup_mode() {
                let mut bits = Vec::new();
                for i in 0..<$gadget as Integer>::SIZE {
                    bits.push(Boolean::from(AllocatedBit::$fn_name(
                        cs.ns(|| format!("allocated bit_gadget {}", i)),
                        || Ok(false),
                    )?));
                }
                Ok(Self::new(bits, None))
            } else {
                let value = value_gen().map(|val| *val.borrow());
                let values = match value {
                    Ok(mut val) => {
                        let mut v = Vec::with_capacity(<$gadget as Integer>::SIZE);

                        for _ in 0..<$gadget as Integer>::SIZE {
                            v.push(Some(val & 1 == 1));
                            val >>= 1;
                        }

                        v
                    }
                    _ => vec![None; <$gadget as Integer>::SIZE],
                };

                let bits = values
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| {
                        Ok(Boolean::from(AllocatedBit::$fn_name(
                            &mut cs.ns(|| format!("allocated bit_gadget {}", i)),
                            || v.ok_or(SynthesisError::AssignmentMissing),
                        )?))
                    })
                    .collect::<Result<Vec<_>, SynthesisError>>()?;

                Ok(Self::new(bits, value.ok()))
            }
        }
    };
}

macro_rules! alloc_gadget_int_impl {
    ($($gadget: ident)*) => ($(
        impl<F: Field> AllocGadget<<$gadget as Integer>::IntegerType, F> for $gadget {
            alloc_gadget_fn_impl!($gadget, alloc);
            alloc_gadget_fn_impl!($gadget, alloc_input);
        }
    )*)
}

alloc_gadget_int_impl!(UInt8);
