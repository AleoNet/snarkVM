// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<E: Environment> CastLossy<Address<E>> for Field<E> {
    /// Casts a `Field` to an `Address`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Address<E>> {
        self.cast()
    }
}

impl<E: Environment> CastLossy<Boolean<E>> for Field<E> {
    /// Casts a `Field` to a `Boolean`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Boolean<E>> {
        match self.to_bits_be().pop() {
            Some(bit) => Ok(Boolean::new(bit)),
            None => bail!("Failed to retrieve the LSB from the field element."),
        }
    }
}

impl<E: Environment> CastLossy<Field<E>> for Field<E> {
    /// Casts a `Field` to a `Field`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Field<E>> {
        self.cast()
    }
}

impl<E: Environment> CastLossy<Group<E>> for Field<E> {
    /// Casts a `Field` to a `Group`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Group<E>> {
        self.cast()
    }
}

// A simple macro to implement `Cast` on types that have the method `from_field_lossy`.
macro_rules! impl_cast {
    ($type:ty) => {
        impl<E: Environment> CastLossy<$type> for Field<E> {
            #[inline]
            fn cast_lossy(&self) -> Result<$type> {
                <$type>::from_field_lossy(self)
            }
        }
    };
}

impl_cast!(I8<E>);
impl_cast!(I16<E>);
impl_cast!(I32<E>);
impl_cast!(I64<E>);
impl_cast!(I128<E>);
impl_cast!(Scalar<E>);
impl_cast!(U8<E>);
impl_cast!(U16<E>);
impl_cast!(U32<E>);
impl_cast!(U64<E>);
impl_cast!(U128<E>);
