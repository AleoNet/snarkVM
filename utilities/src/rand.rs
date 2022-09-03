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

use rand::{
    distributions::{Distribution, Standard},
    rngs::StdRng,
    Rng,
    SeedableRng,
};
use rand_xorshift::XorShiftRng;

/// A trait for a uniform random number generator.
pub trait Uniform: Sized {
    /// Samples a random value from a uniform distribution.
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self;
}

impl<T> Uniform for T
where
    Standard: Distribution<T>,
{
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        rng.sample(Standard)
    }
}

/// A fast RNG used **solely** for testing and benchmarking, **not** for any real world purposes.
pub struct TestRng(XorShiftRng);

impl TestRng {
    pub fn fixed(seed: u64) -> Self {
        // Print the seed, so it's displayed if any of the tests using `test_rng` fails.
        println!("\nInitializing 'TestRng' with seed '{seed}'\n");

        // Use the seed to initialize a fast, non-cryptographic Rng.
        Self(XorShiftRng::seed_from_u64(seed))
    }
}

impl Default for TestRng {
    fn default() -> Self {
        // Obtain the initial seed using entropy provided by the OS.
        let seed = StdRng::from_entropy().gen();

        // Use it as the basis for the underlying Rng.
        Self::fixed(seed)
    }
}

impl rand::RngCore for TestRng {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.0.try_fill_bytes(dest)
    }
}

impl rand::CryptoRng for TestRng {}
