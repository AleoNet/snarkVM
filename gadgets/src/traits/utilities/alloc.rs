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

use crate::utilities::{
    boolean::{AllocatedBit, Boolean},
    int::*,
    integral::Integral,
    uint::*,
};
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::borrow::Borrow;

pub trait AllocBytesGadget<V: ?Sized, F: Field>: Sized
where
    V: Into<Option<Vec<u8>>>,
{
    fn alloc_bytes<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError>;

    fn alloc_bytes_checked<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_bytes(cs, f)
    }

    fn alloc_input_bytes<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError>;

    fn alloc_input_bytes_checked<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_input_bytes(cs, f)
    }
}

pub trait AllocGadget<V: ?Sized, F: Field>: Sized {
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError>;

    fn alloc_checked<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Self::alloc(cs, f)
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError>;

    fn alloc_input_checked<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<V>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Self::alloc_input(cs, f)
    }
}

impl<I, F: Field, A: AllocGadget<I, F>> AllocGadget<[I], F> for Vec<A> {
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<[I]>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = f()?;
        let mut vec = Vec::with_capacity(f.borrow().len());
        for (i, value) in f.borrow().iter().enumerate() {
            vec.push(A::alloc(&mut cs.ns(|| format!("alloc_{}", i)), || Ok(value))?);
        }
        Ok(vec)
    }

    fn alloc_checked<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<[I]>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = f()?;
        let mut vec = Vec::with_capacity(f.borrow().len());
        for (i, value) in f.borrow().iter().enumerate() {
            vec.push(A::alloc_checked(&mut cs.ns(|| format!("alloc_checked_{}", i)), || {
                Ok(value)
            })?);
        }
        Ok(vec)
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<[I]>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = f()?;
        let mut vec = Vec::with_capacity(f.borrow().len());
        for (i, value) in f.borrow().iter().enumerate() {
            vec.push(A::alloc_input(&mut cs.ns(|| format!("alloc_input_{}", i)), || {
                Ok(value)
            })?);
        }
        Ok(vec)
    }

    fn alloc_input_checked<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<[I]>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = f()?;
        let mut vec = Vec::with_capacity(f.borrow().len());
        for (i, value) in f.borrow().iter().enumerate() {
            vec.push(A::alloc_input_checked(
                &mut cs.ns(|| format!("alloc_input_checked_{}", i)),
                || Ok(value),
            )?);
        }
        Ok(vec)
    }
}

macro_rules! alloc_gadget_fn_impl {
    ($gadget: ident, $fn_name: ident) => {
        fn $fn_name<
            Fn: FnOnce() -> Result<T, SynthesisError>,
            T: Borrow<<$gadget as Integral>::IntegerType>,
            CS: ConstraintSystem<F>,
        >(
            mut cs: CS,
            value_gen: Fn,
        ) -> Result<Self, SynthesisError> {
            let value = value_gen().map(|val| *val.borrow());
            let values = match value {
                Ok(mut val) => {
                    let mut v = Vec::with_capacity(<$gadget as Integral>::SIZE);

                    for _ in 0..<$gadget as Integral>::SIZE {
                        v.push(Some(val & 1 == 1));
                        val >>= 1;
                    }

                    v
                }
                _ => vec![None; <$gadget as Integral>::SIZE],
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
    };
}

macro_rules! alloc_gadget_int_impl {
    ($($gadget: ident)*) => ($(
        impl<F: Field> AllocGadget<<$gadget as Integral>::IntegerType, F> for $gadget {
            alloc_gadget_fn_impl!($gadget, alloc);

            alloc_gadget_fn_impl!($gadget, alloc_input);
        }
    )*)
}

alloc_gadget_int_impl!(Int8 Int16 Int32 Int64 Int128 UInt8 UInt16 UInt32 UInt64 UInt128);
