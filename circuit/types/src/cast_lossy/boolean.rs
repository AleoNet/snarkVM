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

// A macro that implements `CastLossy` by invoking `cast`.
// This is safe because casting from a boolean to any other type is **always** lossless.
macro_rules! impl_cast_lossy {
    ($type:ty) => {
        impl<E: Environment> CastLossy<$type> for Boolean<E> {
            fn cast_lossy(&self) -> $type {
                self.cast()
            }
        }
    };
}

impl_cast_lossy!(Address<E>);
impl_cast_lossy!(Field<E>);
impl_cast_lossy!(Group<E>);
impl_cast_lossy!(I8<E>);
impl_cast_lossy!(I16<E>);
impl_cast_lossy!(I32<E>);
impl_cast_lossy!(I64<E>);
impl_cast_lossy!(I128<E>);
impl_cast_lossy!(Scalar<E>);
impl_cast_lossy!(U8<E>);
impl_cast_lossy!(U16<E>);
impl_cast_lossy!(U32<E>);
impl_cast_lossy!(U64<E>);
impl_cast_lossy!(U128<E>);
