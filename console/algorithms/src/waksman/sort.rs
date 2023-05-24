// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use std::collections::HashMap;

impl<E: Environment> ASWaksman<E> {
    /// Returns the sorted `inputs` sequence and the associated `selectors` for the switches in the network.
    pub fn sort(&self, inputs: &[Field<E>]) -> (Vec<Field<E>>, Vec<Boolean<E>>) {
        // Check that the number of inputs is correct.
        if inputs.len() != self.num_inputs {
            return E::halt(format!("The number of inputs must be exactly {}.", self.num_inputs));
        }

        // TODO: Condense sorting logic
        // Sort the inputs.
        let mut sorted = inputs.to_vec();
        sorted.sort();

        // Map each element in the sorted sequence to its index in the sorted sequence, accounting for duplicates.
        let mut element_counts = HashMap::new();
        let mut indexes = HashMap::new();
        for (i, element) in sorted.iter().enumerate() {
            let count = *element_counts.entry(element).and_modify(|count| *count += 1).or_insert(0usize);
            indexes.insert((element, count), i);
        }

        // Construct a vector representing the permutation.
        let mut element_counts = HashMap::new();
        let mut permutation = Vec::with_capacity(self.num_inputs);
        for input in inputs.iter() {
            let count = *element_counts.entry(input).and_modify(|count| *count += 1).or_insert(0usize);
            permutation.push(indexes[&(input, count)]);
        }

        // Construct the selectors for the switches in the network.
        let selectors = self.assign_selectors(&permutation);

        (sorted, selectors)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::iter;

    type CurrentEnvironment = Console;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_sort() {
        // A helper function to run a test that samples a random set of inputs, computes the , and checks that the Waksman network computes the correct permutation.
        fn run_test(n: usize, iterations: usize, rng: &mut TestRng) {
            for i in 0..iterations {
                // Sample a random sequence of inputs.
                let inputs: Vec<Field<CurrentEnvironment>> = iter::repeat_with(|| Uniform::rand(rng)).take(n).collect();
                // Instantiate the Waksman network.
                let network = ASWaksman::<CurrentEnvironment>::new(n);
                // Use the network to sort the inputs.
                let (sorted, selectors) = network.sort(&inputs);
                // Check that the sorted sequence is correct.
                let expected_outputs: Vec<Field<CurrentEnvironment>> = inputs.iter().cloned().sorted().collect();
                assert_eq!(sorted, expected_outputs, "Sort(Iteration: {}, Inputs: {})", i, inputs.len());
                // Check that the network "checks" the permutation correctly.
                assert!(*network.check_permutation(&inputs, &sorted, &selectors));
            }
        }

        let mut rng = TestRng::default();

        run_test(1, ITERATIONS, &mut rng);
        run_test(2, ITERATIONS, &mut rng);
        run_test(3, ITERATIONS, &mut rng);
        run_test(4, ITERATIONS, &mut rng);
        run_test(5, ITERATIONS, &mut rng);
        run_test(6, ITERATIONS, &mut rng);
        run_test(7, ITERATIONS, &mut rng);
        run_test(8, ITERATIONS, &mut rng);
        run_test(9, ITERATIONS, &mut rng);
        run_test(10, ITERATIONS, &mut rng);
        run_test(11, ITERATIONS, &mut rng);
        run_test(12, ITERATIONS, &mut rng);
        run_test(13, ITERATIONS, &mut rng);
        run_test(14, ITERATIONS, &mut rng);
        run_test(15, ITERATIONS, &mut rng);
        run_test(16, ITERATIONS, &mut rng);
        run_test(17, ITERATIONS, &mut rng);
        run_test(32, ITERATIONS, &mut rng);
        run_test(33, ITERATIONS, &mut rng);
        run_test(64, ITERATIONS, &mut rng);
        run_test(65, ITERATIONS, &mut rng);
        run_test(128, ITERATIONS, &mut rng);
        run_test(129, ITERATIONS, &mut rng);
        run_test(256, ITERATIONS, &mut rng);
        run_test(257, ITERATIONS, &mut rng);
        run_test(512, ITERATIONS, &mut rng);
        run_test(513, ITERATIONS, &mut rng);
        run_test(1024, ITERATIONS, &mut rng);
        run_test(1025, ITERATIONS, &mut rng);
        run_test(2048, ITERATIONS, &mut rng);
        run_test(2049, ITERATIONS, &mut rng);
        run_test(4096, ITERATIONS, &mut rng);
        run_test(4097, ITERATIONS, &mut rng);
    }
}
