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

impl<E: Environment> FromBits for Boolean<E> {
    /// Initializes a new boolean by extracting the first bit from a list of length 1.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        match bits_le.len().is_one() {
            true => Ok(Boolean::new(bits_le[0])),
            false => bail!("Boolean::from_bits_le expects a list of one boolean, found {}", bits_le.len()),
        }
    }

    /// Initializes a new boolean by extracting the first bit from a list of length 1.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        match bits_be.len().is_one() {
            true => Ok(Boolean::new(bits_be[0])),
            false => bail!("Boolean::from_bits_be expects a list of one boolean, found {}", bits_be.len()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 100;

    fn check_from_bits_le() -> Result<()> {
        for i in 1..ITERATIONS {
            // Sample a random element.
            let expected: Boolean<CurrentEnvironment> = Uniform::rand(&mut test_rng());
            let given_bits = expected.to_bits_le();
            assert_eq!(Boolean::<CurrentEnvironment>::size_in_bits(), given_bits.len());

            let candidate = Boolean::<CurrentEnvironment>::from_bits_le(&given_bits)?;
            assert_eq!(expected, candidate);

            // Add excess zero bits.
            let candidate = vec![given_bits, vec![false; i as usize]].concat();
            assert!(Boolean::<CurrentEnvironment>::from_bits_le(&candidate).is_err());
        }
        Ok(())
    }

    fn check_from_bits_be() -> Result<()> {
        for i in 1..ITERATIONS {
            // Sample a random element.
            let expected: Boolean<CurrentEnvironment> = Uniform::rand(&mut test_rng());
            let given_bits = expected.to_bits_be();
            assert_eq!(Boolean::<CurrentEnvironment>::size_in_bits(), given_bits.len());

            let candidate = Boolean::<CurrentEnvironment>::from_bits_be(&given_bits)?;
            assert_eq!(expected, candidate);

            // Add excess zero bits.
            let candidate = vec![vec![false; i as usize], given_bits].concat();
            assert!(Boolean::<CurrentEnvironment>::from_bits_be(&candidate).is_err());
        }
        Ok(())
    }

    #[test]
    fn test_from_bits_le() -> Result<()> {
        check_from_bits_le()
    }

    #[test]
    fn test_from_bits_be() -> Result<()> {
        check_from_bits_be()
    }
}
