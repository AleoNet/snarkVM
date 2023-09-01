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

impl<E: Environment> Cast<Boolean<E>> for Field<E> {
    fn cast(&self) -> Result<Boolean<E>> {
        if self.is_zero() {
            Ok(Boolean::new(false))
        } else if self.is_one() {
            Ok(Boolean::new(true))
        } else {
            bail!("Failed to convert field to boolean: field element is not zero or one")
        }
    }
}

// A simple macro to implement `Cast` on types that implement `FromField`.
macro_rules! impl_cast {
    ($type:ty) => {
        impl<E: Environment> Cast<$type> for Field<E> {
            fn cast(&self) -> Result<$type> {
                <$type>::from_field(self)
            }
        }
    };
}

impl_cast!(Address<E>);
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
