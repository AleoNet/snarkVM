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

impl<E: Environment, I: IntegerType> FromField for Integer<E, I> {
    type Field = Field<E>;

    /// Initialize an integer from a field element.
    fn from_field(field: &Self::Field) -> Result<Self> {
        // Note: We are reconstituting the integer from the base field.
        // This is safe as the number of bits in the integer is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(I::BITS < Field::<E>::size_in_bits() as u64);

        // Convert the field element into bits.
        let bits_le = field.to_bits_le();

        // Extract the integer bits from the field element, **without** a carry bit.
        let (bits_le, zero_bits) = bits_le.split_at(Self::size_in_bits());

        // Ensure the unused upper bits are all zero.
        ensure!(zero_bits.iter().all(|&bit| !bit), "Failed to convert integer to field: upper bits are not zero");

        // Return the integer.
        Self::from_bits_le(bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_from_field<I: IntegerType>() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Integer::<CurrentEnvironment, I>::rand(&mut rng);

            // Perform the operation.
            let candidate = Integer::from_field(&expected.to_field()?)?;
            assert_eq!(expected, candidate);
        }
        Ok(())
    }

    #[test]
    fn test_u8_from_field() -> Result<()> {
        type I = u8;
        check_from_field::<I>()
    }

    #[test]
    fn test_i8_from_field() -> Result<()> {
        type I = i8;
        check_from_field::<I>()
    }

    #[test]
    fn test_u16_from_field() -> Result<()> {
        type I = u16;
        check_from_field::<I>()
    }

    #[test]
    fn test_i16_from_field() -> Result<()> {
        type I = i16;
        check_from_field::<I>()
    }

    #[test]
    fn test_u32_from_field() -> Result<()> {
        type I = u32;
        check_from_field::<I>()
    }

    #[test]
    fn test_i32_from_field() -> Result<()> {
        type I = i32;
        check_from_field::<I>()
    }

    #[test]
    fn test_u64_from_field() -> Result<()> {
        type I = u64;
        check_from_field::<I>()
    }

    #[test]
    fn test_i64_from_field() -> Result<()> {
        type I = i64;
        check_from_field::<I>()
    }

    #[test]
    fn test_u128_from_field() -> Result<()> {
        type I = u128;
        check_from_field::<I>()
    }

    #[test]
    fn test_i128_from_field() -> Result<()> {
        type I = i128;
        check_from_field::<I>()
    }
}
