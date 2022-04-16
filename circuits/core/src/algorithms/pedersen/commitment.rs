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

use snarkvm_circuits_types::prelude::*;

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitmentScheme
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = Boolean<E>;
    type Output = Group<E>;
    type Randomness = Boolean<E>;

    /// Returns the Pedersen commitment of the given input with the given randomness
    /// as an affine group element.
    fn commit(&self, input: &[Self::Input], randomness: &[Self::Randomness]) -> Self::Output {
        let hash = self.hash_uncompressed(input);

        // Compute h^r
        randomness
            .iter()
            .zip_eq(&self.random_base)
            .map(|(bit, power)| Group::ternary(bit, power, &Group::zero()))
            .fold(hash, |acc, x| acc + x)
    }
}

impl<'a, E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    Count<dyn CommitmentScheme<Input = Boolean<E>, Output = Group<E>, Randomness = Boolean<E>>>
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Case = (Vec<Mode>, Vec<Mode>);

    fn count(parameters: &Self::Case) -> CircuitCount {
        let (input_modes, randomness_modes) = parameters;
        let uncompressed_count = count!(Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, input_modes);
        let uncompressed_mode = output_mode!(Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, input_modes);

        // Compute the const of constructing the group elements.
        let group_initialize_count = randomness_modes
            .iter()
            .map(|mode| {
                count!(
                    Group<E>,
                    Ternary<Boolean = Boolean<E>, Output = Group<E>>,
                    &(*mode, Mode::Constant, Mode::Constant)
                )
            })
            .fold(CircuitCount::exact(0, 0, 0, 0), |cummulative, count| cummulative.compose(&count));

        // Determine the modes of each of the group elements.
        let modes = randomness_modes.iter().map(|mode| {
            // The `first` and `second` inputs to `Group::ternary` are always constant so we can directly determine the mode instead of
            // using the `output_mode` macro. This avoids the need to use `CircuitOrMode` as a parameter, simplifying the logic of this function.
            match mode.is_constant() {
                true => Mode::Constant,
                false => Mode::Private,
            }
        });

        // Calculate the cost of summing the group elements.
        let (_, summation_count) =
            modes.fold((uncompressed_mode, CircuitCount::exact(0, 0, 0, 0)), |(prev_mode, cumulative), curr_mode| {
                let mode = output_mode!(Group<E>, Add<Group<E>, Output = Group<E>>, &(prev_mode, curr_mode));
                let sum_count = count!(Group<E>, Add<Group<E>, Output = Group<E>>, &(prev_mode, curr_mode));
                (mode, cumulative.compose(&sum_count))
            });

        // Compute the cost of summing the hash and random elements.
        uncompressed_count.compose(&group_initialize_count).compose(&summation_count)
    }
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    OutputMode<dyn CommitmentScheme<Input = Boolean<E>, Output = Group<E>, Randomness = Boolean<E>>>
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Case = (Vec<Mode>, Vec<Mode>);

    fn output_mode(parameters: &Self::Case) -> Mode {
        let (input_modes, randomness_modes) = parameters;
        match input_modes.iter().all(|m| *m == Mode::Constant) && randomness_modes.iter().all(|m| *m == Mode::Constant)
        {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{
        commitment::PedersenCommitment as NativePedersenCommitment,
        CommitmentScheme as NativeCommitmentScheme,
    };
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{test_rng, ToBits as NativeToBits, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "PedersenCommitmentCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;
    type ScalarField = <Circuit as Environment>::ScalarField;

    fn check_commitment<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(mode: Mode) {
        // Initialize the Pedersen hash.
        let native = NativePedersenCommitment::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Sample randomness
            let randomness = ScalarField::rand(&mut test_rng());
            // Compute the expected hash.
            let expected = native.commit(&input, &randomness).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);
            // Prepare the circuit randomness.
            let circuit_randomness: Vec<Boolean<_>> = Inject::new(mode, randomness.to_bits_le());

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.commit(&circuit_input, &circuit_randomness);
                assert_eq!(expected, candidate.eject_value());

                // Check constraint counts and output mode.
                let input_modes = circuit_input.iter().map(|b| b.eject_mode()).collect::<Vec<_>>();
                let randomness_modes = circuit_randomness.iter().map(|b| b.eject_mode()).collect::<Vec<_>>();
                assert_count!(
                    Pedersen<Circuit, NUM_WINDOWS, WINDOW_SIZE>,
                    CommitmentScheme<Input = Boolean<Circuit>, Output = Group<Circuit>, Randomness = Boolean<Circuit>>,
                    &(input_modes.clone(), randomness_modes.clone())
                );
                assert_output_mode!(
                    candidate,
                    Pedersen<Circuit, NUM_WINDOWS, WINDOW_SIZE>,
                    CommitmentScheme<Input = Boolean<Circuit>, Output = Group<Circuit>, Randomness = Boolean<Circuit>>,
                    &(input_modes, randomness_modes)
                );
            });
        }
    }

    #[test]
    fn test_commitment_constant() {
        // Set the number of windows, and modulate the window size.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_commitment::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_commitment::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_commitment::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);
        check_commitment::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Constant);

        // Set the window size, and modulate the number of windows.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_commitment::<2, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_commitment::<3, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_commitment::<4, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
        check_commitment::<5, WINDOW_SIZE_MULTIPLIER>(Mode::Constant);
    }

    #[test]
    fn test_commitment_public() {
        // Set the number of windows, and modulate the window size.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_commitment::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_commitment::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_commitment::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);
        check_commitment::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Public);

        // Set the window size, and modulate the number of windows.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_commitment::<2, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_commitment::<3, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_commitment::<4, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
        check_commitment::<5, WINDOW_SIZE_MULTIPLIER>(Mode::Public);
    }

    #[test]
    fn test_commitment_private() {
        // Set the number of windows, and modulate the window size.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_commitment::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_commitment::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_commitment::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);
        check_commitment::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(Mode::Private);

        // Set the window size, and modulate the number of windows.
        check_commitment::<1, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_commitment::<2, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_commitment::<3, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_commitment::<4, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
        check_commitment::<5, WINDOW_SIZE_MULTIPLIER>(Mode::Private);
    }

    fn check_homomorphic_addition<C: Display + Eject + Add<Output = C> + ToBits<Boolean = Boolean<Circuit>>>(
        pedersen: &impl CommitmentScheme<Input = Boolean<Circuit>, Randomness = Boolean<Circuit>, Output = Group<Circuit>>,
        first: C,
        second: C,
    ) {
        println!("Checking homomorphic addition on {} + {}", first, second);

        // Sample randomness
        let first_randomness = ScalarField::rand(&mut test_rng());
        let second_randomness = ScalarField::rand(&mut test_rng());
        // Prepare the circuit randomness.
        let first_circuit_randomness: Vec<Boolean<_>> = Inject::new(Mode::Private, first_randomness.to_bits_le());
        let second_circuit_randomness: Vec<Boolean<_>> = Inject::new(Mode::Private, second_randomness.to_bits_le());

        // Compute the expected commitment, by committing them individually and summing their results.
        let a = pedersen.commit(&first.to_bits_le(), &first_circuit_randomness);
        let b = pedersen.commit(&second.to_bits_le(), &second_circuit_randomness);
        let expected = a + b;

        let combined_randomness = first_randomness + second_randomness;
        let circuit_combined_randomness: Vec<Boolean<_>> = Inject::new(Mode::Private, combined_randomness.to_bits_le());

        // Sum the two integers, and then commit the sum.
        let candidate = pedersen.commit(&(first + second).to_bits_le(), &circuit_combined_randomness);
        assert_eq!(expected.eject(), candidate.eject());
        assert!(Circuit::is_satisfied());
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
            pedersen: &impl CommitmentScheme<
                Input = Boolean<Circuit>,
                Randomness = Boolean<Circuit>,
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

        // Check Pedersen256.
        let pedersen256 = Pedersen256::setup("Pedersen256HomomorphismTest");
        check_pedersen_homomorphism(&pedersen256);

        // Check Pedersen512.
        let pedersen512 = Pedersen512::setup("Pedersen512HomomorphismTest");
        check_pedersen_homomorphism(&pedersen512);

        // Check Pedersen1024.
        let pedersen1024 = Pedersen1024::setup("Pedersen1024HomomorphismTest");
        check_pedersen_homomorphism(&pedersen1024);
    }
}
