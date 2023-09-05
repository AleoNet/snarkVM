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

impl<E: Environment> CastLossy<Address<E>> for Scalar<E> {
    #[inline]
    fn cast_lossy(&self) -> Result<Address<E>> {
        self.cast()
    }
}

impl<E: Environment> CastLossy<Boolean<E>> for Scalar<E> {
    #[inline]
    fn cast_lossy(&self) -> Result<Boolean<E>> {
        match self.to_bits_be().pop() {
            Some(bit) => Ok(Boolean::new(bit)),
            None => bail!("Failed to retrieve the LSB from the field element."),
        }
    }
}

impl<E: Environment> CastLossy<Group<E>> for Scalar<E> {
    #[inline]
    fn cast_lossy(&self) -> Result<Group<E>> {
        self.cast()
    }
}

impl<E: Environment> CastLossy<Field<E>> for Scalar<E> {
    #[inline]
    fn cast_lossy(&self) -> Result<Field<E>> {
        self.cast()
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Integer<E, I>> for Scalar<E> {
    #[inline]
    fn cast_lossy(&self) -> Result<Integer<E, I>> {
        let bits_le = self.to_bits_le();
        // Use the appropriate lower bits.
        Integer::<E, I>::from_bits_le(&bits_le[0..usize::try_from(I::BITS)?])
    }
}
