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

mod assign;
mod check;
mod sort;
mod switch;

use snarkvm_console_types::prelude::*;

use core::marker::PhantomData;

/// An arbitrary-size Waksman network.
/// See "On Arbitrary Waksman Networks and their Vulnerability" - https://hal.inria.fr/inria-00072871/document
pub struct ASWaksman<E: Environment> {
    /// The number of inputs to the network.
    num_inputs: usize,
    _phantom: PhantomData<E>,
}

impl<E: Environment> ASWaksman<E> {
    /// Initializes a new `ASWaksman` network with the given number of inputs.
    pub fn new(num_inputs: usize) -> Self {
        match num_inputs != 0 {
            true => Self { num_inputs, _phantom: Default::default() },
            false => E::halt("A Waksman network must have at least one input."),
        }
    }

    /// Runs the network on the given sequence of `inputs` using the given `selectors`.
    pub fn run(&self, inputs: &[Field<E>], selectors: &[Boolean<E>]) -> Vec<Field<E>> {
        // Check that the number of inputs is correct.
        if inputs.len() != self.num_inputs {
            return E::halt(format!("The number of inputs must be exactly {}.", self.num_inputs));
        }

        // Check that the number of selectors is correct.
        if selectors.len() != self.num_selectors() {
            return E::halt(format!("The number of selectors must be exactly {}.", self.num_selectors()));
        }

        match self.num_inputs {
            // Base Case #1: The network has exactly one input.
            // In this case, the network is a single wire.
            1 => vec![inputs[0]],
            // Base Case #2: The network has exactly two inputs.
            // In this case, the network is a single switch.
            2 => {
                let result = Self::switch(&selectors[0], &inputs[0], &inputs[1]);
                vec![result.0, result.1]
            }
            _ => {
                // Initialize a counter for the selector bit.
                let mut selector_counter = 0;

                // Calculate the number of inputs to the upper subnetwork.
                let upper_num_inputs = self.num_inputs / 2;
                // Calculate the number of inputs to the lower subnetwork.
                let lower_num_inputs = self.num_inputs - upper_num_inputs;

                // Initialize the upper subnetwork.
                let upper_network = Self::new(upper_num_inputs);
                // Initialize the lower subnetwork.
                let lower_network = Self::new(lower_num_inputs);

                // Calculate the number of input switches.
                let num_input_switches = self.num_inputs / 2;
                // Calculate the number of output switches.
                let num_output_switches = match self.num_inputs % 2 == 0 {
                    true => self.num_inputs / 2 - 1,
                    false => (self.num_inputs - 1) / 2,
                };
                // Check that the number of switches matches the number of selectors.
                if num_input_switches
                    + num_output_switches
                    + upper_network.num_selectors()
                    + lower_network.num_selectors()
                    != self.num_selectors()
                {
                    return E::halt("The number of switches does not match the number of selectors.");
                }

                // Run each pair of inputs through a switch.
                // Arrange the writes into the inputs for the upper and lower subnetworks.
                // Note that if the number of inputs is odd, the last input is not paired with anything.
                let (upper_inputs, lower_inputs) = {
                    // Initialize a vector for the upper subnetwork.
                    let mut upper_inputs = Vec::with_capacity(upper_num_inputs);
                    // Initialize a vector for the lower subnetwork.
                    let mut lower_inputs = Vec::with_capacity(lower_num_inputs);
                    // Initialize a counter to track where we are in the input vector.
                    let mut input_counter = 0;
                    // Run each pair of inputs through a switch, and write the outputs to the appropriate subnetwork.
                    while input_counter < self.num_inputs {
                        if input_counter == self.num_inputs - 1 {
                            // If we are at the last input, write it to the lower subnetwork.
                            lower_inputs.push(inputs[input_counter]);
                            break;
                        } else {
                            let first = &inputs[input_counter];
                            let second = &inputs[input_counter + 1];
                            let (upper, lower) = Self::switch(&selectors[selector_counter], first, second);
                            upper_inputs.push(upper);
                            lower_inputs.push(lower);
                            selector_counter += 1;
                            input_counter += 2;
                        }
                    }
                    (upper_inputs, lower_inputs)
                };

                // Run the upper subnetwork.
                let mut upper_outputs = upper_network.run(
                    &upper_inputs,
                    &selectors[num_input_switches..(num_input_switches + upper_network.num_selectors())],
                );

                // Run the lower subnetwork.
                let mut lower_outputs = lower_network.run(
                    &lower_inputs,
                    &selectors[(num_input_switches + upper_network.num_selectors())
                        ..(num_input_switches + upper_network.num_selectors() + lower_network.num_selectors())],
                );

                // Combine the outputs of the subnetworks.
                let (pairs, additional) = {
                    // Note that the unwraps are safe since, since there are at least 3 inputs to the network, which implies that there is at
                    // least one input/output in each of the subnetworks.
                    match self.num_inputs % 2 == 0 {
                        true => {
                            let second_to_last = upper_outputs.pop().unwrap();
                            let last = lower_outputs.pop().unwrap();
                            let pairs = upper_outputs.into_iter().zip_eq(lower_outputs.into_iter()).collect::<Vec<_>>();
                            (pairs, vec![second_to_last, last])
                        }
                        false => {
                            let last = lower_outputs.pop().unwrap();
                            let pairs = upper_outputs.into_iter().zip_eq(lower_outputs.into_iter()).collect::<Vec<_>>();
                            (pairs, vec![last])
                        }
                    }
                };

                // Run each pair through a switch.
                let mut outputs = {
                    // Set the selector counter.
                    selector_counter =
                        num_input_switches + upper_network.num_selectors() + lower_network.num_selectors();
                    let mut outputs = Vec::with_capacity(self.num_inputs);
                    for (first, second) in pairs {
                        let (upper, lower) = Self::switch(&selectors[selector_counter], &first, &second);
                        outputs.push(upper);
                        outputs.push(lower);
                        selector_counter += 1;
                    }
                    outputs
                };

                // Add the additional output(s).
                outputs.extend(additional);

                outputs
            }
        }
    }

    /// Returns the exact number of selector bits required to program the network.
    pub fn num_selectors(&self) -> usize {
        (1..=self.num_inputs).map(|i| i.next_power_of_two().ilog2() as usize).sum()
    }
}

/// A helper function to invert a permutation.
/// `inverse[i] = j` indicates `permutation` maps the element in the i-th position of the j-th position.
fn invert_permutation(permutation: &[usize]) -> Vec<usize> {
    permutation.iter().enumerate().map(|(i, &j)| (j, i)).sorted().map(|(_, i)| i).collect()
}

#[cfg(test)]
mod test {
    use super::*;

    use snarkvm_utilities::{TestRng, Uniform};

    use rand::seq::SliceRandom;
    use std::iter;

    const ITERATIONS: usize = 100;

    type CurrentEnvironment = Console;

    #[test]
    fn test_random_networks() {
        // A helper function to run a test that samples random permutations, assigns selectors, and checks that the Waksman network computes the correct permutation.
        fn run_test(n: usize, iterations: usize, rng: &mut TestRng) {
            for i in 0..iterations {
                // Sample a random permutation.
                let mut permutation: Vec<usize> = (0..n).collect();
                permutation.shuffle(rng);
                // Compute the inverse permutation.
                let inverse_permutation = invert_permutation(&permutation);
                // Sample a random sequence of inputs.
                let inputs: Vec<Field<CurrentEnvironment>> = iter::repeat_with(|| Uniform::rand(rng)).take(n).collect();
                // Instantiate the Waksman network.
                let network = ASWaksman::<CurrentEnvironment>::new(n);
                // Compute the selectors.
                let selectors = network.assign_selectors(&permutation);
                assert_eq!(selectors.len(), network.num_selectors());
                // Apply the permutation to the inputs.
                let mut expected_outputs = Vec::with_capacity(n);
                for i in 0..inputs.len() {
                    expected_outputs.push(inputs[inverse_permutation[i]]);
                }
                // Run the Waksman network.
                let actual_outputs = network.run(&inputs, &selectors);
                // Check that the outputs are correct.
                assert_eq!(
                    actual_outputs,
                    expected_outputs,
                    "AssignSelectors(Iteration: {}, Inputs: {})",
                    i,
                    inputs.len()
                )
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

    #[test]
    fn test_identity_network() {
        fn run_test(num_inputs: usize, rng: &mut TestRng) {
            for _ in 0..ITERATIONS {
                let network = ASWaksman::new(num_inputs);

                let inputs = iter::repeat_with(|| Field::<CurrentEnvironment>::new(Uniform::rand(rng)))
                    .take(num_inputs)
                    .collect::<Vec<_>>();

                let selectors = vec![Boolean::new(false); network.num_selectors()];

                let outputs = network.run(&inputs, &selectors);
                for (input, output) in inputs.iter().zip_eq(outputs.iter()) {
                    assert_eq!(input, output);
                }
            }
        }

        let mut rng = TestRng::default();

        run_test(1, &mut rng);
        run_test(2, &mut rng);
        run_test(3, &mut rng);
        run_test(4, &mut rng);
        run_test(5, &mut rng);
        run_test(6, &mut rng);
        run_test(7, &mut rng);
        run_test(8, &mut rng);
        run_test(9, &mut rng);
        run_test(10, &mut rng);
        run_test(11, &mut rng);
        run_test(12, &mut rng);
        run_test(13, &mut rng);
        run_test(14, &mut rng);
        run_test(15, &mut rng);
        run_test(16, &mut rng);
        run_test(17, &mut rng);
        run_test(32, &mut rng);
        run_test(33, &mut rng);
        run_test(64, &mut rng);
        run_test(65, &mut rng);
        run_test(128, &mut rng);
        run_test(129, &mut rng);
        run_test(256, &mut rng);
        run_test(257, &mut rng);
        run_test(512, &mut rng);
        run_test(513, &mut rng);
        run_test(1024, &mut rng);
        run_test(1025, &mut rng);
        run_test(2048, &mut rng);
        run_test(2049, &mut rng);
        run_test(4096, &mut rng);
        run_test(4097, &mut rng);
    }

    #[test]
    fn test_reverse_network() {
        fn run_test(num_inputs: usize, rng: &mut TestRng) {
            for _ in 0..ITERATIONS {
                let network = ASWaksman::new(num_inputs);

                let inputs = iter::repeat_with(|| Field::<CurrentEnvironment>::new(Uniform::rand(rng)))
                    .take(num_inputs)
                    .collect::<Vec<_>>();
                let selectors = network.assign_selectors(&(0..num_inputs).rev().collect::<Vec<_>>());

                let outputs = network.run(&inputs, &selectors);
                for (input, output) in inputs.iter().zip_eq(outputs.iter().rev()) {
                    assert_eq!(input, output);
                }
            }
        }

        let mut rng = TestRng::default();

        run_test(1, &mut rng);
        run_test(2, &mut rng);
        run_test(3, &mut rng);
        run_test(4, &mut rng);
        run_test(5, &mut rng);
        run_test(6, &mut rng);
        run_test(7, &mut rng);
        run_test(8, &mut rng);
        run_test(9, &mut rng);
        run_test(10, &mut rng);
        run_test(11, &mut rng);
        run_test(12, &mut rng);
        run_test(13, &mut rng);
        run_test(14, &mut rng);
        run_test(15, &mut rng);
        run_test(16, &mut rng);
        run_test(17, &mut rng);
        run_test(32, &mut rng);
        run_test(33, &mut rng);
        run_test(64, &mut rng);
        run_test(65, &mut rng);
        run_test(128, &mut rng);
        run_test(129, &mut rng);
        run_test(256, &mut rng);
        run_test(257, &mut rng);
        run_test(512, &mut rng);
        run_test(513, &mut rng);
        run_test(1024, &mut rng);
        run_test(1025, &mut rng);
        run_test(2048, &mut rng);
        run_test(2049, &mut rng);
        run_test(4096, &mut rng);
        run_test(4097, &mut rng);
    }

    #[test]
    #[should_panic]
    fn test_zero_size_network_fails() {
        ASWaksman::<CurrentEnvironment>::new(0);
    }
}
