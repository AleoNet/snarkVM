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

impl<E: Environment, const NUM_BITS: u8> Hash for Pedersen<E, NUM_BITS> {
    type Input = Boolean<E>;
    type Output = Field<E>;

    /// Returns the Pedersen hash of the given input as a field element.
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        // Compute the Pedersen hash as an affine group element, and return the x-coordinate.
        self.hash_uncompressed(input).to_x_coordinate()
    }
}

impl<E: Environment, const NUM_BITS: u8> Metrics<dyn Hash<Input = Boolean<E>, Output = Field<E>>>
    for Pedersen<E, NUM_BITS>
{
    type Case = Vec<Mode>;

    #[inline]
    fn count(case: &Self::Case) -> Count {
        count!(Pedersen<E, NUM_BITS>, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, case)
    }
}

impl<E: Environment, const NUM_BITS: u8> OutputMode<dyn Hash<Input = Boolean<E>, Output = Field<E>>>
    for Pedersen<E, NUM_BITS>
{
    type Case = Vec<Mode>;

    #[inline]
    fn output_mode(parameter: &Self::Case) -> Mode {
        output_mode!(Pedersen<E, NUM_BITS>, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, parameter)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, Uniform};

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "PedersenCircuit0";
    const NUM_BITS_MULTIPLIER: u8 = 8;

    fn check_hash<const NUM_BITS: u8>(mode: Mode) {
        use console::Hash as H;

        // Initialize the Pedersen hash.
        let native = console::Pedersen::<<Circuit as Environment>::Network, NUM_BITS>::setup(MESSAGE);
        let circuit = Pedersen::<Circuit, NUM_BITS>::constant(native.clone());

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..NUM_BITS).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Compute the expected hash.
            let expected = native.hash(&input).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.hash(&circuit_input);
                assert_eq!(expected, candidate.eject_value());

                // Check constraint counts and output mode.
                let modes = circuit_input.iter().map(|b| b.eject_mode()).collect::<Vec<_>>();
                assert_count!(
                    Pedersen<Circuit, NUM_BITS>,
                    HashUncompressed<Input = Boolean<Circuit>, Output = Group<Circuit>>,
                    &modes
                );
                assert_output_mode!(
                    Pedersen<Circuit, NUM_BITS>,
                    HashUncompressed<Input = Boolean<Circuit>, Output = Group<Circuit>>,
                    &modes,
                    candidate
                );
            });
        }
    }

    #[test]
    fn test_hash_constant() {
        // Set the number of windows, and modulate the window size.
        check_hash::<NUM_BITS_MULTIPLIER>(Mode::Constant);
        check_hash::<{ 2 * NUM_BITS_MULTIPLIER }>(Mode::Constant);
        check_hash::<{ 3 * NUM_BITS_MULTIPLIER }>(Mode::Constant);
        check_hash::<{ 4 * NUM_BITS_MULTIPLIER }>(Mode::Constant);
        check_hash::<{ 5 * NUM_BITS_MULTIPLIER }>(Mode::Constant);
    }

    #[test]
    fn test_hash_public() {
        // Set the number of windows, and modulate the window size.
        check_hash::<NUM_BITS_MULTIPLIER>(Mode::Public);
        check_hash::<{ 2 * NUM_BITS_MULTIPLIER }>(Mode::Public);
        check_hash::<{ 3 * NUM_BITS_MULTIPLIER }>(Mode::Public);
        check_hash::<{ 4 * NUM_BITS_MULTIPLIER }>(Mode::Public);
        check_hash::<{ 5 * NUM_BITS_MULTIPLIER }>(Mode::Public);
    }

    #[test]
    fn test_hash_private() {
        // Set the number of windows, and modulate the window size.
        check_hash::<NUM_BITS_MULTIPLIER>(Mode::Private);
        check_hash::<{ 2 * NUM_BITS_MULTIPLIER }>(Mode::Private);
        check_hash::<{ 3 * NUM_BITS_MULTIPLIER }>(Mode::Private);
        check_hash::<{ 4 * NUM_BITS_MULTIPLIER }>(Mode::Private);
        check_hash::<{ 5 * NUM_BITS_MULTIPLIER }>(Mode::Private);
    }
}
