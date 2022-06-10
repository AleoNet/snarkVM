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

impl<N: Network> ToBits for Boolean<N> {
    /// Outputs `self` in a vector.
    fn to_bits_le(&self) -> Vec<bool> {
        vec![**self]
    }

    /// Outputs `self` in a vector.
    fn to_bits_be(&self) -> Vec<bool> {
        vec![**self]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_to_bits_le() {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let boolean: Boolean<CurrentNetwork> = Uniform::rand(&mut test_rng());

            let candidate = boolean.to_bits_le();
            assert_eq!(vec![*boolean], candidate);
            assert_eq!(Boolean::<CurrentNetwork>::size_in_bits(), candidate.len());
        }
    }

    #[test]
    fn test_to_bits_be() {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let boolean: Boolean<CurrentNetwork> = Uniform::rand(&mut test_rng());

            let candidate = boolean.to_bits_be();
            assert_eq!(vec![*boolean], candidate);
            assert_eq!(Boolean::<CurrentNetwork>::size_in_bits(), candidate.len());
        }
    }
}
