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

impl<E: Environment, I: IntegerType> Distribution<Integer<E, I>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Integer<E, I> {
        Integer::new(Uniform::rand(rng))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    use std::collections::HashSet;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10;

    fn check_random<I: IntegerType>() {
        // Initialize a set to store all seen random elements.
        let mut set = HashSet::with_capacity(ITERATIONS as usize);

        // Note: This test technically has a `(1 + 2 + ... + ITERATIONS) / MODULUS` probability of being flaky.
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let integer: Integer<CurrentEnvironment, I> = Uniform::rand(&mut test_rng());
            assert!(!set.contains(&integer));

            // Add the new random value to the set.
            set.insert(integer);
        }
    }

    #[test]
    fn test_random() {
        check_random::<u32>();
        check_random::<u64>();
        check_random::<u128>();

        check_random::<i32>();
        check_random::<i64>();
        check_random::<i128>();
    }
}
