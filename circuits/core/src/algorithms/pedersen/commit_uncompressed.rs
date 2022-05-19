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

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitUncompressed
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = Boolean<E>;
    type Output = Group<E>;
    type Randomness = Scalar<E>;

    /// Returns the Pedersen commitment of the given input with the given randomness
    /// as an affine group element.
    fn commit_uncompressed(&self, input: &[Self::Input], randomizer: &Self::Randomness) -> Self::Output {
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
    Metadata<dyn CommitUncompressed<Input = Boolean<E>, Output = Group<E>, Randomness = Scalar<E>>>
    for Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Case = (
        Vec<Vec<CircuitType<Group<E>>>>,
        Vec<CircuitType<Group<E>>>,
        Vec<CircuitType<Boolean<E>>>,
        CircuitType<Scalar<E>>,
    );
    type OutputType = CircuitType<Group<E>>;

    fn count(case: &Self::Case) -> Count {
        let (bases, random_base, input, randomizer) = case;

        let case = (bases.clone(), input.clone());
        let hash_count = count!(Self, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, &case);
        let hash_type = output_type!(Self, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, case);

        let randomizer_bits_le_count = count!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, randomizer);
        let randomizer_bits_le_type = output_type!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, randomizer.clone());

        randomizer_bits_le_type
            .iter()
            .zip_eq(random_base)
            .map(|(bit, power)| {
                let case = (bit.clone(), power.clone(), CircuitType::from(Group::zero()));
                let count = count!(Group<E>, Ternary<Boolean = Boolean<E>, Output = Group<E>>, &case);
                let output_type = output_type!(Group<E>, Ternary<Boolean = Boolean<E>, Output = Group<E>>, case);
                (count, output_type)
            })
            .fold(
                (hash_count + randomizer_bits_le_count, hash_type),
                |(total_count, prev_type), (partial_count, next_type)| {
                    let case = (prev_type, next_type);
                    let count = count!(Group<E>, Add<Group<E>, Output = Group<E>>, &case);
                    let output_type = output_type!(Group<E>, Add<Group<E>, Output = Group<E>>, case);

                    (total_count + partial_count + count, output_type)
                },
            )
            .0
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (bases, random_base, input, randomizer) = case;

        let case = (bases, input);
        let hash_type = output_type!(Self, HashUncompressed<Input = Boolean<E>, Output = Group<E>>, case);

        let randomizer_bits_le_type = output_type!(Scalar<E>, ToBitsLE<Boolean = Boolean<E>>, randomizer);

        randomizer_bits_le_type
            .into_iter()
            .zip_eq(random_base)
            .map(|(bit, power)| {
                output_type!(
                    Group<E>,
                    Ternary<Boolean = Boolean<E>, Output = Group<E>>,
                    (bit, power, CircuitType::from(Group::zero()))
                )
            })
            .fold(hash_type, |prev_type, next_type| {
                output_type!(Group<E>, Add<Group<E>, Output = Group<E>>, (prev_type, next_type))
            })
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
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 10;
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
            let circuit_randomness: Scalar<_> = Inject::new(mode, randomness);

            Circuit::scope(format!("Pedersen {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.commit_uncompressed(&circuit_input, &circuit_randomness);
                assert_eq!(expected, candidate.eject_value());

                // Check constraint counts and output mode.
                let bases: Vec<Vec<CircuitType<Group<Circuit>>>> =
                    circuit.bases.iter().map(|b| b.iter().map(CircuitType::from).collect()).collect();
                let random_base = circuit.random_base.iter().map(CircuitType::from).collect();
                let input = circuit_input.into_iter().map(CircuitType::from).collect::<Vec<_>>();
                let randomizer = CircuitType::from(circuit_randomness);
                let case = (bases, random_base, input, randomizer);
                assert_count!(
                    Pedersen<Circuit, NUM_WINDOWS, WINDOW_SIZE>,
                    CommitUncompressed<Input = Boolean<Circuit>, Output = Group<Circuit>, Randomness = Scalar<Circuit>>,
                    &case
                );
                assert_output_type!(
                    Pedersen<Circuit, NUM_WINDOWS, WINDOW_SIZE>,
                    CommitUncompressed<Input = Boolean<Circuit>, Output = Group<Circuit>, Randomness = Scalar<Circuit>>,
                    case,
                    candidate
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

    fn check_homomorphic_addition<C: Display + Eject + Add<Output = C> + ToBitsLE<Boolean = Boolean<Circuit>>>(
        pedersen: &impl CommitUncompressed<Input = Boolean<Circuit>, Randomness = Scalar<Circuit>, Output = Group<Circuit>>,
        first: C,
        second: C,
    ) {
        println!("Checking homomorphic addition on {} + {}", first, second);

        // Sample randomness
        let first_randomness = ScalarField::rand(&mut test_rng());
        let second_randomness = ScalarField::rand(&mut test_rng());
        // Prepare the circuit randomness.
        let first_circuit_randomness: Scalar<_> = Inject::new(Mode::Private, first_randomness);
        let second_circuit_randomness: Scalar<_> = Inject::new(Mode::Private, second_randomness);

        // Compute the expected commitment, by committing them individually and summing their results.
        let a = pedersen.commit_uncompressed(&first.to_bits_le(), &first_circuit_randomness);
        let b = pedersen.commit_uncompressed(&second.to_bits_le(), &second_circuit_randomness);
        let expected = a + b;

        let circuit_combined_randomness = first_circuit_randomness + second_circuit_randomness;

        // Sum the two integers, and then commit the sum.
        let candidate = pedersen.commit_uncompressed(&(first + second).to_bits_le(), &circuit_combined_randomness);
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
            pedersen: &impl CommitUncompressed<
                Input = Boolean<Circuit>,
                Randomness = Scalar<Circuit>,
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
