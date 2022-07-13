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

impl<E: Environment, I: IntegerType> FromBytes for Integer<E, I> {
    /// Reads the integer from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self::new(FromBytes::read_le(&mut reader)?))
    }
}

impl<E: Environment, I: IntegerType> ToBytes for Integer<E, I> {
    /// Writes the integer to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.integer.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_bytes<I: IntegerType>() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random integer.
            let expected: Integer<CurrentEnvironment, I> = Uniform::rand(&mut test_rng());

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, Integer::read_le(&expected_bytes[..])?);
            assert!(Integer::<CurrentEnvironment, I>::read_le(&expected_bytes[1..]).is_err());

            // Dereference the integer and compare bytes.
            let deref_bytes = (*expected).to_bytes_le()?;
            for (expected, candidate) in expected_bytes.iter().zip_eq(&deref_bytes) {
                assert_eq!(expected, candidate);
            }
        }
        Ok(())
    }

    #[test]
    fn test_bytes() -> Result<()> {
        check_bytes::<u8>()?;
        check_bytes::<u16>()?;
        check_bytes::<u32>()?;
        check_bytes::<u64>()?;
        check_bytes::<u128>()?;

        check_bytes::<i8>()?;
        check_bytes::<i16>()?;
        check_bytes::<i32>()?;
        check_bytes::<i64>()?;
        check_bytes::<i128>()?;

        Ok(())
    }
}
