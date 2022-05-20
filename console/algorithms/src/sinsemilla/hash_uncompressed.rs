// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

use std::borrow::Cow;

impl<E: Environment, const NUM_WINDOWS: u8> HashUncompressed for Sinsemilla<E, NUM_WINDOWS> {
    type Input = bool;
    type Output = Group<E>;

    fn hash_uncompressed(&self, input: &[Self::Input]) -> Result<Self::Output> {
        // Ensure the input size is within the size bounds.
        let mut input = Cow::Borrowed(input);
        let max_len = SINSEMILLA_WINDOW_SIZE * NUM_WINDOWS as usize;
        match input.len() <= max_len {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(max_len, false),
            // Ensure the input size is within the parameter size.
            false => E::halt(format!("The Sinsemilla hash input cannot exceed {} bits.", max_len)),
        }

        Ok(input.chunks(SINSEMILLA_WINDOW_SIZE).fold(self.q, |acc, bits| {
            // Recover the bit window as an integer value so we can index into the lookup table.
            let i = bits.iter().rev().fold(0, |mut acc, bit| {
                acc <<= 1;
                if *bit {
                    acc += 1;
                }
                acc
            });
            acc.double() + self.p_lookups[i as usize]
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_types::environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 1000;
    const MESSAGE: &str = "SinsemillaTest";

    #[test]
    fn test_sinsemilla256_input_size() -> Result<()> {
        let mut rng = TestRng::default();
        let sinsemilla = Sinsemilla256::<CurrentEnvironment>::setup(MESSAGE);
        for _ in 0..ITERATIONS {
            let input = (0..256).map(|_| bool::rand(&mut rng)).collect::<Vec<_>>();
            sinsemilla.hash_uncompressed(&input)?;
        }
        Ok(())
    }

    #[test]
    fn test_sinsemilla512_input_size() -> Result<()> {
        let mut rng = TestRng::default();
        let sinsemilla = Sinsemilla512::<CurrentEnvironment>::setup(MESSAGE);
        for _ in 0..ITERATIONS {
            let input = (0..512).map(|_| bool::rand(&mut rng)).collect::<Vec<_>>();
            sinsemilla.hash_uncompressed(&input)?;
        }
        Ok(())
    }

    #[test]
    fn test_sinsemilla768_input_size() -> Result<()> {
        let mut rng = TestRng::default();
        let sinsemilla = Sinsemilla768::<CurrentEnvironment>::setup(MESSAGE);
        for _ in 0..ITERATIONS {
            let input = (0..768).map(|_| bool::rand(&mut rng)).collect::<Vec<_>>();
            sinsemilla.hash_uncompressed(&input)?;
        }
        Ok(())
    }

    #[test]
    fn test_sinsemilla1024_input_size() -> Result<()> {
        let mut rng = TestRng::default();
        let sinsemilla = Sinsemilla1024::<CurrentEnvironment>::setup(MESSAGE);
        for _ in 0..ITERATIONS {
            let input = (0..1024).map(|_| bool::rand(&mut rng)).collect::<Vec<_>>();
            sinsemilla.hash_uncompressed(&input)?;
        }
        Ok(())
    }
}
