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

impl<E: Environment> ASWaksman<E> {
    /// Returns the sorted `inputs` sequence and the associated `selectors` for the switches in the network.
    pub fn sort(&self, inputs: &[Field<E>]) -> (Vec<Field<E>>, Vec<Boolean<E>>) {
        // Check that the number of inputs is correct.
        if inputs.len() != self.num_inputs {
            return E::halt(format!("The number of inputs must be exactly {}.", self.num_inputs));
        }

        // Sort the inputs.
        // `sorted_with_original_index` is a sorted vector of tuples where the first element is the input and the second element is the original index of the input.
        let sorted_with_original_index =
            inputs.iter().enumerate().map(|(i, input)| (*input, i)).sorted().collect::<Vec<_>>();
        // Get the sorted sequence.
        // `sorted` is a vector of the sorted inputs.
        let sorted = sorted_with_original_index.iter().map(|(input, _)| *input).collect::<Vec<_>>();
        // Get the permutation, which is a mapping from the original index to the sorted index.
        let permutation = sorted_with_original_index
            .iter()
            .enumerate()
            .map(|(j, (_, i))| (*i, j))
            .sorted()
            .map(|(_, j)| j)
            .collect::<Vec<_>>();
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
