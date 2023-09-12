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

impl<E: Environment> Cast<Address<E>> for Boolean<E> {
    /// Casts a `Boolean` to an `Address`.
    #[inline]
    fn cast(&self) -> Result<Address<E>> {
        let field: Field<E> = self.cast()?;
        field.cast()
    }
}

impl<E: Environment> Cast<Boolean<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Boolean`.
    #[inline]
    fn cast(&self) -> Result<Boolean<E>> {
        Ok(*self)
    }
}

impl<E: Environment> Cast<Field<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Field`.
    #[inline]
    fn cast(&self) -> Result<Field<E>> {
        match **self {
            true => Ok(Field::one()),
            false => Ok(Field::zero()),
        }
    }
}

impl<E: Environment> Cast<Group<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Group`.
    #[inline]
    fn cast(&self) -> Result<Group<E>> {
        let field: Field<E> = self.cast()?;
        field.cast()
    }
}

impl<E: Environment, I: IntegerType> Cast<Integer<E, I>> for Boolean<E> {
    /// Casts a `Boolean` to an `Integer`.
    #[inline]
    fn cast(&self) -> Result<Integer<E, I>> {
        match **self {
            true => Ok(Integer::one()),
            false => Ok(Integer::zero()),
        }
    }
}

impl<E: Environment> Cast<Scalar<E>> for Boolean<E> {
    /// Casts a `Boolean` to a `Scalar`.
    #[inline]
    fn cast(&self) -> Result<Scalar<E>> {
        match **self {
            true => Ok(Scalar::one()),
            false => Ok(Scalar::zero()),
        }
    }
}
