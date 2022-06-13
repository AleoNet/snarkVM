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

impl<E: Environment, I: IntegerType> FromFields for Integer<E, I> {
    type Field = Field<E>;

    /// Initializes a new integer by recovering the **x-coordinate** of an affine group from a field element.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        // Ensure there is exactly one field element in the vector.
        ensure!(fields.len() == 1, "Integer must be recovered from a single field element");
        // Recover the integer from the field element.
        Self::from_field(&fields[0])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_from_fields<I: IntegerType>() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random integer.
            let expected = Integer::<CurrentEnvironment, I>::rand(&mut test_rng());

            // Perform the operation.
            let candidate = Integer::from_fields(&expected.to_fields()?)?;
            assert_eq!(expected, candidate);
        }
        Ok(())
    }

    #[test]
    fn test_u8_from_fields() -> Result<()> {
        type I = u8;
        check_from_fields::<I>()
    }

    #[test]
    fn test_i8_from_fields() -> Result<()> {
        type I = i8;
        check_from_fields::<I>()
    }

    #[test]
    fn test_u16_from_fields() -> Result<()> {
        type I = u16;
        check_from_fields::<I>()
    }

    #[test]
    fn test_i16_from_fields() -> Result<()> {
        type I = i16;
        check_from_fields::<I>()
    }

    #[test]
    fn test_u32_from_fields() -> Result<()> {
        type I = u32;
        check_from_fields::<I>()
    }

    #[test]
    fn test_i32_from_fields() -> Result<()> {
        type I = i32;
        check_from_fields::<I>()
    }

    #[test]
    fn test_u64_from_fields() -> Result<()> {
        type I = u64;
        check_from_fields::<I>()
    }

    #[test]
    fn test_i64_from_fields() -> Result<()> {
        type I = i64;
        check_from_fields::<I>()
    }

    #[test]
    fn test_u128_from_fields() -> Result<()> {
        type I = u128;
        check_from_fields::<I>()
    }

    #[test]
    fn test_i128_from_fields() -> Result<()> {
        type I = i128;
        check_from_fields::<I>()
    }
}
