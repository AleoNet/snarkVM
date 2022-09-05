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

impl<E: Environment> Distribution<StringType<E>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> StringType<E> {
        // Sample a random number up to 1/4 of the maximum bytes.
        let num_bytes = rng.gen_range(1..(E::MAX_STRING_BYTES / 4) as usize);
        // Sample a random string.
        StringType::new(&rng.sample_iter(&Alphanumeric).take(num_bytes).map(char::from).collect::<String>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    use std::collections::HashSet;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_random() {
        // Initialize a set to store all seen random elements.
        let mut set = HashSet::with_capacity(ITERATIONS as usize);

        // Note: This test technically has a `(1 + 2 + ... + ITERATIONS) / MODULUS` probability of being flaky.
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let string: StringType<CurrentEnvironment> = Uniform::rand(&mut test_crypto_rng());
            assert!(!set.contains(&string), "{}", string);

            // Add the new random value to the set.
            set.insert(string);
        }
    }
}
