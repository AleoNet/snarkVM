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
use crate::Cast;

impl<E: Environment, I: IntegerType> CastLossy<Address<E>> for Integer<E, I> {
    fn cast_lossy(&self) -> Address<E> {
        self.cast()
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Boolean<E>> for Integer<E, I> {
    fn cast_lossy(&self) -> Boolean<E> {
        match self.to_bits_be().pop() {
            Some(bit) => bit,
            None => E::halt("Failed to retrieve the LSB from the integer."),
        }
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Field<E>> for Integer<E, I> {
    fn cast_lossy(&self) -> Field<E> {
        self.cast()
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Group<E>> for Integer<E, I> {
    fn cast_lossy(&self) -> Group<E> {
        self.cast()
    }
}

impl<E: Environment, I0: IntegerType, I1: IntegerType> CastLossy<Integer<E, I1>> for Integer<E, I0> {
    fn cast_lossy(&self) -> Integer<E, I1> {
        let mut bits_le = self.to_bits_le();
        // If the target integer type has few bits, use the appropriate lower bits.
        match I0::BITS <= I1::BITS {
            true => Integer::<E, I1>::from_bits_le(&bits_le),
            false => Integer::<E, I1>::from_bits_le(&bits_le[0..(I1::BITS as usize)]),
        }
    }
}

impl<E: Environment, I: IntegerType> CastLossy<Scalar<E>> for Integer<E, I> {
    fn cast_lossy(&self) -> Scalar<E> {
        self.cast()
    }
}
