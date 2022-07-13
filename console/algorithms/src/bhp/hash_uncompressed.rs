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

impl<E: Environment, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> HashUncompressed
    for BHP<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = bool;
    type Output = Group<E>;

    /// Returns the BHP hash of the given input as an affine group element.
    ///
    /// This uncompressed variant of the BHP hash function is provided to support
    /// the BHP commitment scheme, as it is typically not used by applications.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Result<Self::Output> {
        // The number of hasher bits to fit.
        let num_hasher_bits = NUM_WINDOWS as usize * WINDOW_SIZE as usize * BHP_CHUNK_SIZE;
        // The number of data bits in the output.
        let num_data_bits = Field::<E>::size_in_data_bits();
        // The maximum number of input bits per iteration.
        let max_input_bits_per_iteration = num_hasher_bits - num_data_bits;

        // Initialize a variable to store the hash from the current iteration.
        let mut digest = Group::<E>::zero();

        // Compute the hash of the input.
        for (i, input_bits) in input.chunks(max_input_bits_per_iteration).enumerate() {
            // Initialize a vector for the hash preimage.
            let mut preimage = Vec::with_capacity(num_hasher_bits);
            // Determine if this is the first iteration.
            match i == 0 {
                // Construct the first iteration as: [ 0...0 || DOMAIN || LENGTH(INPUT) || INPUT[0..BLOCK_SIZE] ].
                true => {
                    preimage.extend(&self.domain);
                    preimage.extend((input.len() as u64).to_bits_le());
                    preimage.extend(input_bits);
                }
                // Construct the subsequent iterations as: [ PREVIOUS_HASH[0..DATA_BITS] || INPUT[I * BLOCK_SIZE..(I + 1) * BLOCK_SIZE] ].
                false => {
                    preimage.extend(digest.to_x_coordinate().to_bits_le().iter().take(num_data_bits));
                    preimage.extend(input_bits);
                }
            }
            // Hash the preimage for this iteration.
            digest = self.hasher.hash_uncompressed(&preimage)?;
        }

        Ok(digest)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_types::environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_bhp256_input_size() -> Result<()> {
        let bhp = BHP256::<CurrentEnvironment>::setup("BHPTest")?;
        for i in 0..ITERATIONS {
            let input = (0..bhp.window_size() as u64 + i).map(|_| bool::rand(&mut test_rng())).collect::<Vec<_>>();
            bhp.hash_uncompressed(&input)?;
        }
        Ok(())
    }

    #[test]
    fn test_bhp512_input_size() -> Result<()> {
        let bhp = BHP512::<CurrentEnvironment>::setup("BHPTest")?;
        for i in 0..ITERATIONS {
            let input = (0..bhp.window_size() as u64 + i).map(|_| bool::rand(&mut test_rng())).collect::<Vec<_>>();
            bhp.hash_uncompressed(&input)?;
        }
        Ok(())
    }

    #[test]
    fn test_bhp768_input_size() -> Result<()> {
        let bhp = BHP768::<CurrentEnvironment>::setup("BHPTest")?;
        for i in 0..ITERATIONS {
            let input = (0..bhp.window_size() as u64 + i).map(|_| bool::rand(&mut test_rng())).collect::<Vec<_>>();
            bhp.hash_uncompressed(&input)?;
        }
        Ok(())
    }

    #[test]
    fn test_bhp1024_input_size() -> Result<()> {
        let bhp = BHP1024::<CurrentEnvironment>::setup("BHPTest")?;
        for i in 0..ITERATIONS {
            let input = (0..bhp.window_size() as u64 + i).map(|_| bool::rand(&mut test_rng())).collect::<Vec<_>>();
            bhp.hash_uncompressed(&input)?;
        }
        Ok(())
    }
}
