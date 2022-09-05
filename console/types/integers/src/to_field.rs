// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use super::*;

impl<E: Environment, I: IntegerType> ToField for Integer<E, I> {
    type Field = Field<E>;

    /// Converts an integer into a field element.
    fn to_field(&self) -> Result<Self::Field> {
        // Note: We are reconstituting the integer as a base field.
        // This is safe as the number of bits in the integer is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(I::BITS < Field::<E>::size_in_bits() as u64);

        // Reconstruct the bits as a linear combination representing the original field value.
        Field::from_bits_le(&self.to_bits_le())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_to_field<I: IntegerType>() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Integer::<CurrentEnvironment, I>::rand(&mut test_rng());

            // Perform the operation.
            let candidate = expected.to_field()?;

            // Extract the bits from the base field representation.
            let candidate_bits_le = candidate.to_bits_le();
            assert_eq!(Field::<CurrentEnvironment>::size_in_bits(), candidate_bits_le.len());

            // Ensure all integer bits match with the expected result.
            let expected_bits = expected.to_bits_le();
            for (expected_bit, candidate_bit) in expected_bits.iter().zip_eq(&candidate_bits_le[0..I::BITS as usize]) {
                assert_eq!(expected_bit, candidate_bit);
            }

            // Ensure all remaining bits are 0.
            for candidate_bit in &candidate_bits_le[I::BITS as usize..] {
                assert!(!candidate_bit);
            }
        }
        Ok(())
    }

    #[test]
    fn test_u8_to_field() -> Result<()> {
        type I = u8;
        check_to_field::<I>()
    }

    #[test]
    fn test_i8_to_field() -> Result<()> {
        type I = i8;
        check_to_field::<I>()
    }

    #[test]
    fn test_u16_to_field() -> Result<()> {
        type I = u16;
        check_to_field::<I>()
    }

    #[test]
    fn test_i16_to_field() -> Result<()> {
        type I = i16;
        check_to_field::<I>()
    }

    #[test]
    fn test_u32_to_field() -> Result<()> {
        type I = u32;
        check_to_field::<I>()
    }

    #[test]
    fn test_i32_to_field() -> Result<()> {
        type I = i32;
        check_to_field::<I>()
    }

    #[test]
    fn test_u64_to_field() -> Result<()> {
        type I = u64;
        check_to_field::<I>()
    }

    #[test]
    fn test_i64_to_field() -> Result<()> {
        type I = i64;
        check_to_field::<I>()
    }

    #[test]
    fn test_u128_to_field() -> Result<()> {
        type I = u128;
        check_to_field::<I>()
    }

    #[test]
    fn test_i128_to_field() -> Result<()> {
        type I = i128;
        check_to_field::<I>()
    }
}
