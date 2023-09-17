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

impl<E: Environment, I: IntegerType> CastLossy<Address<E>> for Integer<E, I> {
    /// Casts an `Integer` to an `Address`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Address<E>> {
        self.cast()
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Boolean<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Boolean`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Boolean<E>> {
        match self.to_bits_be().pop() {
            Some(bit) => Ok(Boolean::new(bit)),
            None => bail!("Failed to retrieve the LSB from the integer."),
        }
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Field<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Field`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Field<E>> {
        self.cast()
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Group<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Group`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Group<E>> {
        self.cast()
    }
}

impl<E: Environment, I0: IntegerType + AsPrimitive<I1>, I1: IntegerType> CastLossy<Integer<E, I1>> for Integer<E, I0> {
    /// Casts an `Integer` to an `Integer` of a different type, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Integer<E, I1>> {
        Ok(Integer::new((**self).as_()))
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Scalar<E>> for Integer<E, I> {
    /// Casts an `Integer` to a `Scalar`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Result<Scalar<E>> {
        self.cast()
    }
}
