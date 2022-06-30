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

impl<E: Environment, I: IntegerType> ToFields for Integer<E, I> {
    type Field = Field<E>;

    /// Returns the integer as field elements.
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        Ok(vec![self.to_field()?])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_to_fields<I: IntegerType>() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Integer::<CurrentEnvironment, I>::rand(&mut test_rng());

            // Perform the operation.
            let candidate = expected.to_fields()?;

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
    fn test_u8_to_fields() -> Result<()> {
        type I = u8;
        check_to_fields::<I>()
    }

    #[test]
    fn test_i8_to_fields() -> Result<()> {
        type I = i8;
        check_to_fields::<I>()
    }

    #[test]
    fn test_u16_to_fields() -> Result<()> {
        type I = u16;
        check_to_fields::<I>()
    }

    #[test]
    fn test_i16_to_fields() -> Result<()> {
        type I = i16;
        check_to_fields::<I>()
    }

    #[test]
    fn test_u32_to_fields() -> Result<()> {
        type I = u32;
        check_to_fields::<I>()
    }

    #[test]
    fn test_i32_to_fields() -> Result<()> {
        type I = i32;
        check_to_fields::<I>()
    }

    #[test]
    fn test_u64_to_fields() -> Result<()> {
        type I = u64;
        check_to_fields::<I>()
    }

    #[test]
    fn test_i64_to_fields() -> Result<()> {
        type I = i64;
        check_to_fields::<I>()
    }

    #[test]
    fn test_u128_to_fields() -> Result<()> {
        type I = u128;
        check_to_fields::<I>()
    }

    #[test]
    fn test_i128_to_fields() -> Result<()> {
        type I = i128;
        check_to_fields::<I>()
    }
}
