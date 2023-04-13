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

mod check;

use crate::CheckPermutation;

use snarkvm_circuit_types::prelude::*;

use core::marker::PhantomData;

/// An arbitrary-size Waksman network.
/// See "On Arbitrary Waksman Networks and their Vulnerability" - https://hal.inria.fr/inria-00072871/document
pub struct ASWaksman<E: Environment> {
    /// The number of inputs to the network.
    // TODO: u32?
    num_inputs: u64,
    _phantom: PhantomData<E>,
}

impl<E: Environment> ASWaksman<E> {
    /// Initializes a new `ASWaksman` network of the given size.
    pub fn new(size: u64) -> Self {
        if size == 0 {
            E::halt("The size of a Waksman network must be greater than zero.")
        }
        Self { num_inputs: size, _phantom: Default::default() }
    }

    /// Runs the network on the given sequence of `inputs` using the given `selectors`.
    pub fn run(&self, inputs: &[Field<E>], selectors: &[Boolean<E>]) -> Vec<Field<E>> {
        // Check that the number of inputs is correct.
        if inputs.len() as u64 != self.num_inputs {
            E::halt(format!("The number of inputs must be exactly {}.", self.num_inputs));
        }

        // Check that the number of selectors is correct.
        if selectors.len() as u64 != self.num_selectors() {
            E::halt(format!("The number of selectors must be exactly {}.", self.num_selectors()));
        }

        match self.num_inputs {
            // Base Case #1: The network has exactly one input.
            // In this case, the network is a single wire.
            1 => vec![inputs[0].clone()],
            // Base Case #2: The network has exactly two inputs.
            // In this case, the network is a single switch.
            2 => {
                let result = Self::switch(&inputs[0], &inputs[1], &selectors[0]);
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
                let mut upper_network = Self::new(upper_num_inputs);
                // Initialize the lower subnetwork.
                let mut lower_network = Self::new(lower_num_inputs);

                // Calculate the number of input switches.
                let num_input_switches = self.num_inputs / 2;
                // Calculate the number of output switches.
                let num_output_switches = match self.num_inputs.is_even() {
                    true => self.num_inputs / 2 - 1,
                    false => (self.num_inputs - 1) / 2,
                };
                // Check that the number of switches matches the number of selectors.
                if num_input_switches + num_output_switches + upper.num_selectors() + lower.num_selectors()
                    != self.num_selectors()
                {
                    E::halt("The number of switches does not match the number of selectors.");
                }

                // Run each pair of inputs through a switch.
                // Arrange the writes into the inputs for the upper and lower subnetworks.
                // Note that if the number of inputs is odd, the last input is not paired with anything.
                let (upper_inputs, lower_inputs) = {
                    // Initialize a vector for the upper subnetwork.
                    let mut upper_inputs = Vec::with_capacity(upper_num_inputs as usize);
                    // Initialize a vector for the lower subnetwork.
                    let mut lower_inputs = Vec::with_capacity(lower_num_inputs as usize);
                    // Initialize a counter to track where we are in the input vector.
                    let mut input_counter = 0;
                    // Run each pair of inputs through a switch, and write the outputs to the appropriate subnetwork.
                    while input_counter < self.num_inputs {
                        if input_counter == self.num_inputs - 1 {
                            // If we are at the last input, write it to the lower subnetwork.
                            lower_inputs.push(inputs[input_counter].clone());
                            break;
                        } else {
                            let first = &inputs[input_counter];
                            let second = &inputs[input_counter + 1];
                            let (upper, lower) = Self::switch(first, second, &selectors[selector_counter]);
                            upper_inputs.push(upper);
                            lower_inputs.push(lower);
                            selector_counter += 1;
                            input_counter += 2;
                        }
                    }
                };

                // Run the upper subnetwork.
                let mut upper_outputs = upper_network.run(
                    &upper_inputs,
                    &selectors[num_input_switches..(num_input_switches + upper_network.num_selectors())],
                );

                // Run the lower subnetwork.
                let mut lower_output = lower_network.run(
                    &lower_inputs,
                    &selectors[(num_input_switches + upper_network.num_selectors())
                        ..(num_input_switches + upper_network.num_selectors() + lower_network.num_selectors())],
                );

                // Combine the outputs of the subnetworks.
                let (pairs, additional) = {
                    match self.num_inputs.is_even() {
                        true => {
                            // TODO: Unwrap safety
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
                        (num_input_switches + upper_network.num_selectors() + lower_network.num_selectors()) as usize;
                    // TODO: Off by a few
                    let mut outputs = Vec::with_capacity(self.num_inputs as usize);
                    for (first, second) in pairs {
                        let (upper, lower) = Self::switch(&first, &second, &selectors[selector_counter]);
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
    pub const fn num_selectors(&self) -> u64 {
        (1..=self.num_inputs).map(|i| i.next_power_of_two().ilog2()).sum()
    }

    /// A helper function to construct a switch in the network.
    /// The switch takes two inputs, `first` and `second`, and returns a pair of outputs.
    /// The output pair is determined by the `selector` bit.
    /// If the selector is `true`, the first output is `second` and the second output is `first`.
    /// If the selector is `false`, the first output is `first` and the second output is `second`.
    fn switch(first: &Field<E>, second: &Field<E>, selector: &Boolean<E>) -> (Field<E>, Field<E>) {
        (Field::ternary(selector, second, first), Field::ternary(selector, first, second))
    }
}
