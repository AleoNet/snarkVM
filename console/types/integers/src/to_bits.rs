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

impl<E: Environment, I: IntegerType> ToBits for Integer<E, I> {
    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<bool> {
        (**self).to_bits_le()
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<bool> {
        (**self).to_bits_be()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_to_bits_le<I: IntegerType>() {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let integer: Integer<CurrentEnvironment, I> = Uniform::rand(&mut test_rng());

            let candidate = integer.to_bits_le();
            assert_eq!(Integer::<CurrentEnvironment, I>::size_in_bits(), candidate.len());

            for (expected, candidate) in (*integer).to_bits_le().iter().zip_eq(&candidate) {
                assert_eq!(expected, candidate);
            }
        }
    }

    fn check_to_bits_be<I: IntegerType>() {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let integer: Integer<CurrentEnvironment, I> = Uniform::rand(&mut test_rng());

            let candidate = integer.to_bits_be();
            assert_eq!(Integer::<CurrentEnvironment, I>::size_in_bits(), candidate.len());

            for (expected, candidate) in (*integer).to_bits_be().iter().zip_eq(&candidate) {
                assert_eq!(expected, candidate);
            }
        }
    }

    #[test]
    fn test_to_bits_le() {
        check_to_bits_le::<u8>();
        check_to_bits_le::<u16>();
        check_to_bits_le::<u32>();
        check_to_bits_le::<u64>();
        check_to_bits_le::<u128>();

        check_to_bits_le::<i8>();
        check_to_bits_le::<i16>();
        check_to_bits_le::<i32>();
        check_to_bits_le::<i64>();
        check_to_bits_le::<i128>();
    }

    #[test]
    fn test_to_bits_be() {
        check_to_bits_be::<u8>();
        check_to_bits_be::<u16>();
        check_to_bits_be::<u32>();
        check_to_bits_be::<u64>();
        check_to_bits_be::<u128>();

        check_to_bits_be::<i8>();
        check_to_bits_be::<i16>();
        check_to_bits_be::<i32>();
        check_to_bits_be::<i64>();
        check_to_bits_be::<i128>();
    }
}
