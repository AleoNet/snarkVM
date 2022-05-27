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

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitUncompressed
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = Boolean<E>;
    type Output = Group<E>;
    type Randomizer = Scalar<E>;

    /// Returns the Pedersen commitment of the given input and randomizer as an affine group element.
    fn commit_uncompressed(&self, input: &[Self::Input], randomizer: &Self::Randomizer) -> Self::Output {
        let hash = self.hash_uncompressed(input);

        // Compute h^r
        randomizer
            .to_bits_le()
            .iter()
            .zip_eq(&self.random_base)
            .map(|(bit, power)| Group::ternary(bit, power, &Group::zero()))
            .fold(hash, |acc, x| acc + x)
    }
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    Metrics<dyn CommitUncompressed<Input = Boolean<E>, Output = Group<E>, Randomizer = Scalar<E>>>
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Case = (Vec<Mode>, Vec<Mode>);

    fn count(case: &Self::Case) -> Count {
        let (input_modes, randomizer_modes) = case;
        let uncompressed_count = count!(Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, input_modes);
        let uncompressed_mode = output_mode!(Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, input_modes);

        // Compute the const of constructing the group elements.
        let group_initialize_count = randomizer_modes
            .iter()
            .map(|mode| {
                count!(
                    Group<E>,
                    Ternary<Boolean = Boolean<E>, Output = Group<E>>,
                    &(*mode, Mode::Constant, Mode::Constant)
                )
            })
            .fold(Count::zero(), |cumulative, count| cumulative + count);

        // Determine the modes of each of the group elements.
        let modes = randomizer_modes.iter().map(|mode| {
            // The `first` and `second` inputs to `Group::ternary` are always constant so we can directly determine the mode instead of
            // using the `output_mode` macro. This avoids the need to use `CircuitType` as a parameter, simplifying the logic of this function.
            match mode.is_constant() {
                true => Mode::Constant,
                false => Mode::Private,
            }
        });

        // Calculate the cost of summing the group elements.
        let (_, summation_count) =
            modes.fold((uncompressed_mode, Count::zero()), |(prev_mode, cumulative), curr_mode| {
                let mode = output_mode!(Group<E>, Add<Group<E>, Output = Group<E>>, &(prev_mode, curr_mode));
                let sum_count = count!(Group<E>, Add<Group<E>, Output = Group<E>>, &(prev_mode, curr_mode));
                (mode, cumulative + sum_count)
            });

        // Compute the cost of summing the hash and random elements.
        uncompressed_count + group_initialize_count + summation_count
    }
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    OutputMode<dyn CommitUncompressed<Input = Boolean<E>, Output = Group<E>, Randomizer = Scalar<E>>>
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Case = (Vec<Mode>, Vec<Mode>);

    fn output_mode(parameters: &Self::Case) -> Mode {
        let (input_modes, randomizer_modes) = parameters;
        match input_modes.iter().all(|m| *m == Mode::Constant) && randomizer_modes.iter().all(|m| *m == Mode::Constant)
        {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;
    use snarkvm_console_algorithms::{CommitUncompressed as C, Pedersen as NativePedersen};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "PedersenCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    fn check_commit_uncompressed<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(mode: Mode) {
        // Initialize Pedersen.
        let native = NativePedersen::<<Circuit as Environment>::Affine, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Sample a randomizer.
            let randomizer = UniformRand::rand(&mut test_rng());
            // Compute the expected commitment.
            let expected = native.commit_uncompressed(&input, &randomizer).expect("Failed to commit native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);
            // Prepare the circuit randomizer.
            let circuit_randomizer: Scalar<_> = Inject::new(mode, randomizer);

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                // Perform the commit operation.
                let candidate = circuit.commit_uncompressed(&circuit_input, &circuit_randomizer);
                assert_eq!(expected, candidate.eject_value());

                // Check constraint counts and output mode.
                let input_modes = circuit_input.iter().map(|b| b.eject_mode()).collect::<Vec<_>>();
                let randomizer_modes =
                    circuit_randomizer.to_bits_le().iter().map(|b| b.eject_mode()).collect::<Vec<_>>();
                assert_count!(
                    Pedersen<Circuit, NUM_WINDOWS, WINDOW_SIZE>,
                    CommitUncompressed<Input = Boolean<Circuit>, Output = Group<Circuit>, Randomizer = Scalar<Circuit>>,
                    &(input_modes.clone(), randomizer_modes.clone())
                );
                assert_output_mode!(
                    Pedersen<Circuit, NUM_WINDOWS, WINDOW_SIZE>,
                    CommitUncompressed<Input = Boolean<Circuit>, Output = Group<Circuit>, Randomizer = Scalar<Circuit>>,
                    &(input_modes, randomizer_modes),
                    candidate
                );
            });
        }
    }

    fn check_homomorphic_addition<C: Display + Eject + Add<Output = C> + ToBits<Boolean = Boolean<Circuit>>>(
        pedersen: &impl CommitUncompressed<Input = Boolean<Circuit>, Randomizer = Scalar<Circuit>, Output = Group<Circuit>>,
        first: C,
        second: C,
    ) {
        println!("Checking homomorphic addition on {} + {}", first, second);

        // Sample randomizers.
        let first_randomizer = UniformRand::rand(&mut test_rng());
        let second_randomizer = UniformRand::rand(&mut test_rng());
        // Prepare the circuit randomizers.
        let first_circuit_randomizer: Scalar<_> = Inject::new(Mode::Private, first_randomizer);
        let second_circuit_randomizer: Scalar<_> = Inject::new(Mode::Private, second_randomizer);

        // Compute the expected commitment, by committing them individually and summing their results.
        let a = pedersen.commit_uncompressed(&first.to_bits_le(), &first_circuit_randomizer);
        let b = pedersen.commit_uncompressed(&second.to_bits_le(), &second_circuit_randomizer);
        let expected = a + b;

        let circuit_combined_randomizer = first_circuit_randomizer + second_circuit_randomizer;

        // Sum the two integers, and then commit the sum.
        let candidate = pedersen.commit_uncompressed(&(first + second).to_bits_le(), &circuit_combined_randomizer);
        assert_eq!(expected.eject(), candidate.eject());
        assert!(Circuit::is_satisfied());
    }

    #[test]
    fn test_commit_uncompressed_constant() {
        // Set the number of windows, and modulate the window size.
        check_commit_uncompressed::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_commit_uncompressed::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_commit_uncompressed::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_commit_uncompressed::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_commit_uncompressed::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
    }

    #[test]
    fn test_commit_uncompressed_public() {
        // Set the number of windows, and modulate the window size.
        check_commit_uncompressed::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_commit_uncompressed::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_commit_uncompressed::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_commit_uncompressed::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_commit_uncompressed::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
    }

    #[test]
    fn test_commit_uncompressed_private() {
        // Set the number of windows, and modulate the window size.
        check_commit_uncompressed::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_commit_uncompressed::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_commit_uncompressed::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_commit_uncompressed::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_commit_uncompressed::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
    }

    #[test]
    fn test_pedersen64_homomorphism_private() {
        // Initialize Pedersen64.
        let pedersen = Pedersen64::setup("Pedersen64HomomorphismTest");

        for _ in 0..ITERATIONS {
            // Sample two random unsigned integers, with the MSB set to 0.
            let first = U8::<Circuit>::new(Mode::Private, u8::rand(&mut test_rng()) >> 1);
            let second = U8::new(Mode::Private, u8::rand(&mut test_rng()) >> 1);
            check_homomorphic_addition(&pedersen, first, second);

            // Sample two random unsigned integers, with the MSB set to 0.
            let first = U16::<Circuit>::new(Mode::Private, u16::rand(&mut test_rng()) >> 1);
            let second = U16::new(Mode::Private, u16::rand(&mut test_rng()) >> 1);
            check_homomorphic_addition(&pedersen, first, second);

            // Sample two random unsigned integers, with the MSB set to 0.
            let first = U32::<Circuit>::new(Mode::Private, u32::rand(&mut test_rng()) >> 1);
            let second = U32::new(Mode::Private, u32::rand(&mut test_rng()) >> 1);
            check_homomorphic_addition(&pedersen, first, second);

            // Sample two random unsigned integers, with the MSB set to 0.
            let first = U64::<Circuit>::new(Mode::Private, u64::rand(&mut test_rng()) >> 1);
            let second = U64::new(Mode::Private, u64::rand(&mut test_rng()) >> 1);
            check_homomorphic_addition(&pedersen, first, second);
        }
    }

    #[test]
    fn test_pedersen_homomorphism_private() {
        fn check_pedersen_homomorphism(
            pedersen: &impl CommitUncompressed<
                Input = Boolean<Circuit>,
                Randomizer = Scalar<Circuit>,
                Output = Group<Circuit>,
            >,
        ) {
            for _ in 0..ITERATIONS {
                // Sample two random unsigned integers, with the MSB set to 0.
                let first = U8::<Circuit>::new(Mode::Private, u8::rand(&mut test_rng()) >> 1);
                let second = U8::new(Mode::Private, u8::rand(&mut test_rng()) >> 1);
                check_homomorphic_addition(pedersen, first, second);

                // Sample two random unsigned integers, with the MSB set to 0.
                let first = U16::<Circuit>::new(Mode::Private, u16::rand(&mut test_rng()) >> 1);
                let second = U16::new(Mode::Private, u16::rand(&mut test_rng()) >> 1);
                check_homomorphic_addition(pedersen, first, second);

                // Sample two random unsigned integers, with the MSB set to 0.
                let first = U32::<Circuit>::new(Mode::Private, u32::rand(&mut test_rng()) >> 1);
                let second = U32::new(Mode::Private, u32::rand(&mut test_rng()) >> 1);
                check_homomorphic_addition(pedersen, first, second);

                // Sample two random unsigned integers, with the MSB set to 0.
                let first = U64::<Circuit>::new(Mode::Private, u64::rand(&mut test_rng()) >> 1);
                let second = U64::new(Mode::Private, u64::rand(&mut test_rng()) >> 1);
                check_homomorphic_addition(pedersen, first, second);

                // Sample two random unsigned integers, with the MSB set to 0.
                let first = U128::<Circuit>::new(Mode::Private, u128::rand(&mut test_rng()) >> 1);
                let second = U128::new(Mode::Private, u128::rand(&mut test_rng()) >> 1);
                check_homomorphic_addition(pedersen, first, second);
            }
        }

        // Check Pedersen128.
        let pedersen128 = Pedersen128::setup("Pedersen128HomomorphismTest");
        check_pedersen_homomorphism(&pedersen128);
    }
}
