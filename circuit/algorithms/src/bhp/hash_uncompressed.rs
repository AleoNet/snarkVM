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
    type Input = Boolean<E>;
    type Output = Group<E>;

    /// Returns the BHP hash of the given input as an affine group element.
    ///
    /// This uncompressed variant of the BHP hash function is provided to support
    /// the BHP commitment scheme, as it is typically not used by applications.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Self::Output {
        // The number of hasher bits to fit.
        let num_hasher_bits = NUM_WINDOWS as usize * WINDOW_SIZE as usize * BHP_CHUNK_SIZE;
        // The number of data bits in the output.
        let num_data_bits = E::BaseField::size_in_data_bits();
        // The maximum number of input bits per iteration.
        let max_input_bits_per_iteration = num_hasher_bits - num_data_bits;

        // Initialize a variable to store the hash from the current iteration.
        let mut digest = Group::zero();

        // Compute the hash of the input.
        for (i, input_bits) in input.chunks(max_input_bits_per_iteration).enumerate() {
            // Initialize a vector for the hash preimage.
            let mut preimage = Vec::with_capacity(num_hasher_bits);
            // Determine if this is the first iteration.
            match i == 0 {
                // Construct the first iteration as: [ 0...0 || DOMAIN || LENGTH(INPUT) || INPUT[0..BLOCK_SIZE] ].
                true => {
                    preimage.extend(self.domain.clone());
                    preimage.extend(U64::constant(console::U64::new(input.len() as u64)).to_bits_le());
                    preimage.extend_from_slice(input_bits);
                }
                // Construct the subsequent iterations as: [ PREVIOUS_HASH[0..DATA_BITS] || INPUT[I * BLOCK_SIZE..(I + 1) * BLOCK_SIZE] ].
                false => {
                    preimage.extend(digest.to_x_coordinate().to_bits_le().into_iter().take(num_data_bits));
                    preimage.extend_from_slice(input_bits);
                }
            }
            // Hash the preimage for this iteration.
            digest = self.hasher.hash_uncompressed(&preimage);
        }

        digest
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;
    const DOMAIN: &str = "BHPCircuit0";

    macro_rules! check_hash_uncompressed {
        ($bhp:ident, $mode:ident, $num_bits:expr, ($num_constants:expr, $num_public:expr, $num_private:expr, $num_constraints:expr)) => {{
            // Initialize BHP.
            let native = console::$bhp::<<Circuit as Environment>::Network>::setup(DOMAIN)?;
            let circuit = $bhp::<Circuit>::constant(native.clone());

            for i in 0..ITERATIONS {
                // Sample a random input.
                let input = (0..$num_bits).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>();
                // Compute the expected hash.
                let expected = console::HashUncompressed::hash_uncompressed(&native, &input)?;
                // Prepare the circuit input.
                let circuit_input: Vec<Boolean<_>> = Inject::new(Mode::$mode, input);

                Circuit::scope(format!("BHP {i}"), || {
                    // Perform the hash operation.
                    let candidate = circuit.hash_uncompressed(&circuit_input);
                    assert_scope!($num_constants, $num_public, $num_private, $num_constraints);
                    assert_eq!(expected, candidate.eject_value());
                });
                Circuit::reset();
            }
            Ok::<_, anyhow::Error>(())
        }};
    }

    fn check_hash_uncompressed<const NUM_WINDOWS: u8, const WINDOW_SIZE: u8>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        use console::HashUncompressed as H;

        // Initialize BHP.
        let native = console::BHP::<<Circuit as Environment>::Network, NUM_WINDOWS, WINDOW_SIZE>::setup(DOMAIN)?;
        let circuit = BHP::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::new(Mode::Constant, native.clone());
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS as usize * WINDOW_SIZE as usize * BHP_CHUNK_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Compute the expected hash.
            let expected = native.hash_uncompressed(&input).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);

            Circuit::scope(format!("BHP {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.hash_uncompressed(&circuit_input);
                assert_scope!(num_constants, num_public, num_private, num_constraints);
                assert_eq!(expected, candidate.eject_value());
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_hash_uncompressed_constant() -> Result<()> {
        check_hash_uncompressed::<32, 48>(Mode::Constant, 7311, 0, 0, 0)
    }

    #[test]
    fn test_hash_uncompressed_public() -> Result<()> {
        check_hash_uncompressed::<32, 48>(Mode::Public, 542, 0, 8592, 8593)
    }

    #[test]
    fn test_hash_uncompressed_private() -> Result<()> {
        check_hash_uncompressed::<32, 48>(Mode::Private, 542, 0, 8592, 8593)
    }

    #[test]
    fn test_hash_uncompressed_bhp256_constant() -> Result<()> {
        check_hash_uncompressed!(BHP256, Constant, 261, (762, 0, 0, 0))
    }

    #[test]
    fn test_hash_uncompressed_bhp256_public() -> Result<()> {
        check_hash_uncompressed!(BHP256, Public, 261, (409, 0, 449, 449))
    }

    #[test]
    fn test_hash_uncompressed_bhp256_private() -> Result<()> {
        check_hash_uncompressed!(BHP256, Private, 261, (409, 0, 449, 449))
    }

    #[test]
    fn test_hash_uncompressed_bhp512_constant() -> Result<()> {
        check_hash_uncompressed!(BHP512, Constant, 522, (1125, 0, 0, 0))
    }

    #[test]
    fn test_hash_uncompressed_bhp512_public() -> Result<()> {
        check_hash_uncompressed!(BHP512, Public, 522, (421, 0, 905, 905))
    }

    #[test]
    fn test_hash_uncompressed_bhp512_private() -> Result<()> {
        check_hash_uncompressed!(BHP512, Private, 522, (421, 0, 905, 905))
    }

    #[test]
    fn test_hash_uncompressed_bhp768_constant() -> Result<()> {
        check_hash_uncompressed!(BHP768, Constant, 783, (1518, 0, 0, 0))
    }

    #[test]
    fn test_hash_uncompressed_bhp768_public() -> Result<()> {
        check_hash_uncompressed!(BHP768, Public, 783, (459, 0, 1389, 1389))
    }

    #[test]
    fn test_hash_uncompressed_bhp768_private() -> Result<()> {
        check_hash_uncompressed!(BHP768, Private, 783, (459, 0, 1389, 1389))
    }

    #[test]
    fn test_hash_uncompressed_bhp1024_constant() -> Result<()> {
        check_hash_uncompressed!(BHP1024, Constant, 1043, (1831, 0, 0, 0))?;
        check_hash_uncompressed!(BHP1024, Constant, 1044, (1831, 0, 0, 0))?;
        check_hash_uncompressed!(BHP1024, Constant, 1046, (2433, 0, 0, 0))
    }

    #[test]
    fn test_hash_uncompressed_bhp1024_public() -> Result<()> {
        check_hash_uncompressed!(BHP1024, Public, 1043, (429, 0, 1789, 1789))?;
        check_hash_uncompressed!(BHP1024, Public, 1044, (429, 0, 1789, 1789))?;
        check_hash_uncompressed!(BHP1024, Public, 1046, (438, 0, 2475, 2476))
    }

    #[test]
    fn test_hash_uncompressed_bhp1024_private() -> Result<()> {
        check_hash_uncompressed!(BHP1024, Private, 1043, (429, 0, 1789, 1789))?;
        check_hash_uncompressed!(BHP1024, Private, 1044, (429, 0, 1789, 1789))?;
        check_hash_uncompressed!(BHP1024, Private, 1046, (438, 0, 2475, 2476))
    }

    #[test]
    fn test_hash_uncompressed_cost_comparison() -> Result<()> {
        // The cost to hash 512 bits for each BHP variant is:
        check_hash_uncompressed!(BHP256, Private, 512, (422, 0, 1557, 1558))?;
        check_hash_uncompressed!(BHP512, Private, 512, (421, 0, 890, 890))?;
        check_hash_uncompressed!(BHP768, Private, 512, (447, 0, 918, 918))?;
        check_hash_uncompressed!(BHP1024, Private, 512, (417, 0, 883, 883))
    }
}
