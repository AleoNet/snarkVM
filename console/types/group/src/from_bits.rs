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

impl<E: Environment> FromBits for Group<E> {
    /// Initializes a new group by recovering the **x-coordinate** of an affine group from a list of **little-endian** bits.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        Self::from_x_coordinate(Field::<E>::from_bits_le(bits_le)?)
    }

    /// Initializes a new group by recovering the **x-coordinate** of an affine group from a list of **big-endian** bits.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        Self::from_x_coordinate(Field::<E>::from_bits_be(bits_be)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 100;

    fn check_from_bits_le() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: Group<CurrentEnvironment> = Uniform::rand(&mut test_rng());
            let given_bits = expected.to_bits_le();
            assert_eq!(Group::<CurrentEnvironment>::size_in_bits(), given_bits.len());

            let candidate = Group::<CurrentEnvironment>::from_bits_le(&given_bits)?;
            assert_eq!(expected, candidate);

            // Add excess zero bits.
            let candidate = vec![given_bits, vec![false; i as usize]].concat();

            let candidate = Group::<CurrentEnvironment>::from_bits_le(&candidate)?;
            assert_eq!(expected, candidate);
            assert_eq!(Group::<CurrentEnvironment>::size_in_bits(), candidate.to_bits_le().len());
        }
        Ok(())
    }

    fn check_from_bits_be() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: Group<CurrentEnvironment> = Uniform::rand(&mut test_rng());
            let given_bits = expected.to_bits_be();
            assert_eq!(Group::<CurrentEnvironment>::size_in_bits(), given_bits.len());

            let candidate = Group::<CurrentEnvironment>::from_bits_be(&given_bits)?;
            assert_eq!(expected, candidate);

            // Add excess zero bits.
            let candidate = vec![vec![false; i as usize], given_bits].concat();

            let candidate = Group::<CurrentEnvironment>::from_bits_be(&candidate)?;
            assert_eq!(expected, candidate);
            assert_eq!(Group::<CurrentEnvironment>::size_in_bits(), candidate.to_bits_be().len());
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
