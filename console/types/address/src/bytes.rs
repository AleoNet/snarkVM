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

impl<E: Environment> FromBytes for Address<E> {
    /// Reads in an account address from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Address::new(FromBytes::read_le(&mut reader)?))
    }
}

impl<E: Environment> ToBytes for Address<E> {
    /// Writes an account address to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.address.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_bytes() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let expected = Address::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, Address::read_le(&expected_bytes[..])?);
            assert!(Address::<CurrentEnvironment>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
