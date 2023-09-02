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

impl<E: Environment, I: IntegerType> Cast<Address<E>> for Integer<E, I> {
    fn cast(&self) -> Result<Address<E>> {
        let field: Field<E> = self.cast()?;
        field.cast()
    }
}

impl<E: Environment, I: IntegerType> Cast<Boolean<E>> for Integer<E, I> {
    fn cast(&self) -> Result<Boolean<E>> {
        if self.is_zero() {
            Ok(Boolean::new(false))
        } else if self.is_one() {
            Ok(Boolean::new(true))
        } else {
            bail!("Failed to convert integer to boolean: integer is not zero or one")
        }
    }
}

impl<E: Environment, I: IntegerType> Cast<Field<E>> for Integer<E, I> {
    fn cast(&self) -> Result<Field<E>> {
        self.to_field()
    }
}

impl<E: Environment, I: IntegerType> Cast<Group<E>> for Integer<E, I> {
    fn cast(&self) -> Result<Group<E>> {
        let field: Field<E> = self.cast()?;
        field.cast()
    }
}

impl<E: Environment, I0: IntegerType, I1: IntegerType> Cast<Integer<E, I1>> for Integer<E, I0> {
    fn cast(&self) -> Result<Integer<E, I1>> {
        let mut bits_le = self.to_bits_le();
        match I0::BITS <= I1::BITS {
            // If the target integer type is larger or the same size as the source integer type, then extend the bits appropriately.
            true => {
                match I0::is_signed() {
                    // Sign extend the uppermost bit.
                    true => bits_le.extend(
                        std::iter::repeat(*bits_le.last().unwrap()).take(usize::try_from(I1::BITS - I0::BITS)?),
                    ),
                    // Zero extend the uppermost bit.
                    false => bits_le.extend(std::iter::repeat(false).take(usize::try_from(I1::BITS - I0::BITS)?)),
                }
            }
            // If the target integer type is smaller than the source integer type, then check that the value is within bounds of the
            // target integer type and truncate the bits appropriately.
            false => {
                for bit in bits_le.iter().skip(usize::try_from(I1::BITS)?) {
                    // TODO (d0cd): Check that this logic is correct.
                    match I0::is_signed() {
                        // If the source integer type is signed and the value is negative, then check that the upper bits are set.
                        true if *bits_le.last().unwrap() => {
                            if !*bit {
                                bail!(format!(
                                    "Failed to convert integer '{}' to integer '{}': integer is out of bounds",
                                    I0::type_name(),
                                    I1::type_name()
                                ))
                            }
                        }
                        // Otherwise, check that the upper bits are zero.
                        _ => {
                            if *bit {
                                bail!(format!(
                                    "Failed to convert integer '{}' to integer '{}': integer is out of bounds",
                                    I0::type_name(),
                                    I1::type_name()
                                ))
                            }
                        }
                    }
                }
            }
        };
        Integer::<E, I1>::from_bits_le(&bits_le)
    }
}

impl<E: Environment, I: IntegerType> Cast<Scalar<E>> for Integer<E, I> {
    fn cast(&self) -> Result<Scalar<E>> {
        let mut bits_le = self.to_bits_le();
        bits_le.extend(std::iter::repeat(false).take(Scalar::<E>::size_in_bits() - usize::try_from(I::BITS)?));
        Scalar::<E>::from_bits_le(&bits_le)
    }
}
