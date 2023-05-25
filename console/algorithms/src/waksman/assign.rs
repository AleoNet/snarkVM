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

use petgraph::{
    algo::{condensation, toposort},
    Directed,
    Graph,
};
use std::collections::{BTreeMap, HashSet};

impl<E: Environment> ASWaksman<E> {
    /// Returns the sequence of selector bits that implements the given `permutation`.
    /// `permutation[i] = k` indicates the permutation maps the element in the `i`th position of the input to the `k`th position of the output.
    pub fn assign_selectors(&self, permutation: &[usize]) -> Vec<Boolean<E>> {
        // Check that the size of the permutation correct.
        if permutation.len() != self.num_inputs {
            return E::halt(format!("The size of the permutation must be exactly {}.", self.num_inputs));
        }

        // Check that the `permutation` is valid.
        // For the `permutation` to be valid, the elements must be unique and the largest element must be less than the number of inputs.
        // Note that this unwrap is safe since `self.num_inputs` is always greater than zero.
        let mut permutation_vec = permutation.to_vec();
        permutation_vec.dedup();
        if !(permutation.len() == permutation_vec.len() && permutation.iter().max().unwrap() < &self.num_inputs) {
            return E::halt("Invalid permutation.");
        }

        let selectors = match permutation.len() {
            // Base Case #1: The network has exactly one input.
            // In this case, the network is a single wire, and there are no selectors.
            1 => vec![],
            // Base Case #2: The network has exactly two inputs.
            // In this case, the network is a single switch, and there is exactly one selector.
            2 => vec![Boolean::new(permutation[0] == 1)],
            _ => {
                let mut selectors = Vec::with_capacity(self.num_selectors());
                // Assign inputs to the upper and lower subnetworks, while satisfying the constraints given by the topology of the network.
                // Note that `assign_to_upper_subnet[i] == true` indicates that the i-th input is assigned to the upper subnetwork.
                // By definition, `assign_to_upper_subnet[2i] != assign_to_upper_subnet[2i + 1]`.
                let assign_to_upper_subnet = assign_to_subnets::<E>(permutation);
                // From the assignment, compute the input selectors.
                // For all i, if `assign_to_upper_subnet[2i] == true`, then the selector for the switch must be false.
                selectors.extend(
                    assign_to_upper_subnet.iter().take(permutation.len() / 2 * 2).step_by(2).map(|&b| Boolean::new(!b)),
                );

                // Construct the permutation for the upper and lower subnetworks.
                let mut upper_permutation = Vec::with_capacity(permutation.len() / 2);
                let mut lower_permutation = Vec::with_capacity(permutation.len() - upper_permutation.len());
                for (i, &b) in assign_to_upper_subnet.iter().enumerate() {
                    if b {
                        upper_permutation.push(permutation[i] / 2);
                    } else {
                        lower_permutation.push(permutation[i] / 2);
                    }
                }

                // Compute the selectors for the upper subnetwork.
                selectors.extend(ASWaksman::new(upper_permutation.len()).assign_selectors(&upper_permutation));

                // Compute the selectors for the lower subnetwork.
                selectors.extend(ASWaksman::new(lower_permutation.len()).assign_selectors(&lower_permutation));

                // Compute the inverse of the permutation.
                let inverse_permutation = invert_permutation(permutation);
                // Compute the selectors for the output switches.
                // For all i, except the last, if `assign_to_upper_subnet[inverse_permutation[2i]] == true`, then the selector for the switch must be false.
                for i in 0..((inverse_permutation.len() - 1) / 2) {
                    selectors.push(Boolean::new(!assign_to_upper_subnet[inverse_permutation[2 * i]]));
                }
                selectors
            }
        };

        // If the computed number of selectors does not match the expected number, then halt.
        if selectors.len() != self.num_selectors() {
            return E::halt(format!(
                "The number of selectors is incorrect. Expected {}, found {}.",
                self.num_selectors(),
                selectors.len()
            ));
        }

        selectors
    }
}

/// A helper function that takes a `permutation` and returns a vector of booleans, indicating the subnetwork to which each input is assigned.
/// If `result[i] == true`, then the i-th input is assigned to the upper subnetwork.
/// If `result[i] == false`, then the i-th input is assigned to the lower subnetwork.
fn assign_to_subnets<E: Environment>(permutation: &[usize]) -> Vec<bool> {
    // The assignment to subnetworks is computed by encoding the network topology and desired permutation as an instance of the 2-SAT problem.
    //
    // First,
    // - Let `N` be the number of inputs.
    // - Let `x_i` be a boolean variable for each input `i`, indicating whether or not the input is assigned to the upper subnetwork.
    // - Let `inv: usize -> usize` be the inverse of the permutation, s.t `permutation[i] == j` iff `inv[j] == i`.
    //
    // The encoding is as follows:
    // 1. For each `i` in `0..(N / 2)`, add the clauses:  ( x_{2i} | x_{2i + 1} ) & ( ~x_{2i} | ~x_{2i + 1} ).
    //   These clauses ensure that for every pair of inputs assigned to the same input switch, exactly one of the inputs is assigned to the upper subnetwork.
    // 2. For each `i` in `0..((N - 1)) / 2)`, add the clauses:  ( x_{inv(2i)} | x_{inv(2i + 1)} ) & ( ~x_{inv(2i)} | ~x_{inv(2i + 1)} ).
    //   These clauses ensure that for every pair of outputs assigned to the same output switch, exactly one of the outputs is produced by the upper subnetwork.
    // 3. Add the clause:  ( ~x_{inv(N - 1)} | false )
    //   This clause ensures that the last output is produced by the lower subnetwork.
    // 4. If `N` is even, add the clause:  ( x_{inv(N - 2)} | false )
    //   In the case where the number of inputs is even, this clause ensures that the second-to-last output is produced by the upper subnetwork.
    //
    // The 2-SAT instance is encoded as an implication graph.
    // That is, for each clause `(a | b)` in the 2-SAT instance, the implication graph must have the edges `~b ==> a` and `~a ==> b`.
    // See https://en.wikipedia.org/wiki/2-satisfiability for more details on the graph encoding and how a satisfying assignment is produced.

    // Compute the inverse of the permutation.
    let inverse_permutation = invert_permutation(permutation);

    // Instantiate the implication graph.
    let mut implication_graph =
        Graph::<usize, usize, Directed>::with_capacity(permutation.len() * 2, permutation.len() * 2);

    // Initialize the nodes.
    // Note that the implication graph has `2N` vertices, one for each boolean variable and its negation.
    // Note that `x_i` is represented by the vertex `2i`, and `~x_i` is represented by the vertex `2i + 1`.
    let mut node_indices = Vec::with_capacity(permutation.len() * 2);
    let num_variables = permutation.len() * 2;
    for i in 0..num_variables {
        node_indices.push(implication_graph.add_node(i));
    }

    // Helpers for indexing into the nodes.
    let index = |i: usize| node_indices[2 * i];
    let not_index = |i: usize| node_indices[2 * i + 1];

    // Add clauses for Step 1, as described above.
    for i in 0..(permutation.len() / 2) {
        // Add an edge for the clause:  ( x_{2i} | x_{2i + 1} ).
        // This corresponds to the implications: ~x_{2i + 1} ==> x_{2i} and ~x_{2i} ==> x_{2i + 1}.
        implication_graph.add_edge(not_index(2 * i + 1), index(2 * i), 0);
        implication_graph.add_edge(not_index(2 * i), index(2 * i + 1), 0);
        // Add an edge for the clause:  ( ~x_{2i} | ~x_{2i + 1} ).
        // This corresponds to the implications: x_{2i + 1} ==> ~x_{2i} and x_{2i} ==> ~x_{2i + 1}.
        implication_graph.add_edge(index(2 * i + 1), not_index(2 * i), 0);
        implication_graph.add_edge(index(2 * i), not_index(2 * i + 1), 0);
    }

    // Add clauses for Step 2, as described above.
    for i in 0..((permutation.len() - 1) / 2) {
        // Add an edge for the clause:  ( x_{inv(2i)} | x_{inv(2i + 1)} ).
        // This corresponds to the implications: ~x_{inv(2i + 1)} ==> x_{inv(2i)} and ~x_{inv(2i)} ==> x_{inv(2i + 1)}.
        implication_graph.add_edge(not_index(inverse_permutation[2 * i + 1]), index(inverse_permutation[2 * i]), 0);
        implication_graph.add_edge(not_index(inverse_permutation[2 * i]), index(inverse_permutation[2 * i + 1]), 0);
        // Add an edge for the clause:  ( ~x_{inv(2i)} | ~x_{inv(2i + 1)} ).
        // This corresponds to the implications: x_{inv(2i + 1)} ==> ~x_{inv(2i)} and x_{inv(2i)} ==> ~x_{inv(2i + 1)}.
        implication_graph.add_edge(index(inverse_permutation[2 * i + 1]), not_index(inverse_permutation[2 * i]), 0);
        implication_graph.add_edge(index(inverse_permutation[2 * i]), not_index(inverse_permutation[2 * i + 1]), 0);
    }

    // Add clauses for Step 3, as described above.
    // Add an edge for the clause:  ( ~x_{inv(N - 1)} | ~x_{inv(N - 1)} )
    // This corresponds to the implication: x_{inv(N - 1)} ==> ~x_{inv(N - 1)}
    let last_element_index = inverse_permutation[permutation.len() - 1];
    implication_graph.add_edge(index(last_element_index), not_index(last_element_index), 0);

    // Add clauses for Step 4, as described above.
    if permutation.len() % 2 == 0 {
        // Add an edge for the clause:  ( x_{inv(N - 2)} | x_{inv(N - 2)} )
        // This corresponds to the implications: ~x_{inv(N - 2)} ==> x_{inv(N - 2)}
        let second_last_element_index = inverse_permutation[permutation.len() - 2];
        implication_graph.add_edge(not_index(second_last_element_index), index(second_last_element_index), 0);
    }

    // Compute the condensation of the implication graph.
    let condensation = condensation(implication_graph, true);
    // Get the topological ordering of the condensation.
    // Note that the unwrap is safe since the condensation is guaranteed to be acyclic.
    let topological_order = toposort(&condensation, None).unwrap();

    // A helper function to get the complement of a variable.
    let complement = |i: usize| if i % 2 == 0 { i + 1 } else { i - 1 };

    // An assignment to the variables in the 2-SAT instance.
    let mut assignment = BTreeMap::new();
    // Process each element of the condensation in reverse topological order, check that 2-SAT instance is satisfiable, and construct the satisfying assignment.
    for condensation_index in topological_order.iter().rev() {
        // Check that a variable and its complement are not in the same node in the condensation.
        // Note that the unwrap is safe since `condensation_index` is in the topological ordering of `condensation`.
        let component = condensation.node_weight(*condensation_index).unwrap();
        // Store each variable seen in the component in a set.
        let mut seen = HashSet::with_capacity(component.len());
        for index in component {
            if seen.contains(&complement(*index)) {
                // The 2-SAT instance is not satisfiable.
                return E::halt("Could not find a satisfying assignment for the given permutation.");
            } else {
                // Mark the variable as seen.
                seen.insert(*index);
                // If the variable does not have an assignment, assign it `true`.
                if assignment.get(index).is_some() {
                    // The variable already has an assignment.
                    continue;
                } else {
                    // Assign the variable `true`.
                    assignment.insert(*index, true);
                    // Assign its complement `false`.
                    assignment.insert(complement(*index), false);
                }
            }
        }
    }
    // Return the assignment, ignoring the negations of variables.
    let assignment: Vec<bool> = assignment.into_values().step_by(2).collect();
    assignment
}

#[cfg(test)]
mod test {
    use super::*;

    type CurrentEnvironment = Console;

    // A helper function to test that selectors are computed correctly.
    fn test_selectors(permutation: &[usize], expected_selectors: &[bool]) {
        let network = ASWaksman::<CurrentEnvironment>::new(permutation.len());
        let selectors = network.assign_selectors(permutation);
        assert_eq!(&selectors.into_iter().map(|b| *b).collect_vec(), expected_selectors);
    }

    #[test]
    fn test_assign_selectors_one() {
        test_selectors(&[0], &[]);
    }

    #[test]
    fn test_assign_selectors_two() {
        test_selectors(&[0, 1], &[false]);
        test_selectors(&[1, 0], &[true]);
    }

    #[test]
    fn test_assign_selectors_three() {
        test_selectors(&[0, 1, 2], &[true, false, true]);
        test_selectors(&[0, 2, 1], &[false, true, false]);
        test_selectors(&[1, 0, 2], &[true, false, false]);
        test_selectors(&[1, 2, 0], &[false, true, true]);
        test_selectors(&[2, 0, 1], &[true, true, false]);
        test_selectors(&[2, 1, 0], &[true, true, true]);
    }

    #[test]
    fn test_assign_selectors_four() {
        test_selectors(&[0, 1, 2, 3], &[true, false, false, false, true]);
        test_selectors(&[0, 1, 3, 2], &[true, true, false, false, true]);
        test_selectors(&[0, 2, 1, 3], &[true, false, true, false, true]);
        test_selectors(&[0, 2, 3, 1], &[true, true, true, false, true]);
        test_selectors(&[0, 3, 1, 2], &[false, true, false, true, false]);
        test_selectors(&[0, 3, 2, 1], &[false, false, false, true, false]);
        test_selectors(&[1, 0, 2, 3], &[true, false, false, false, false]);
        test_selectors(&[1, 0, 3, 2], &[true, true, false, false, false]);
        test_selectors(&[1, 2, 0, 3], &[true, false, true, false, false]);
        test_selectors(&[1, 2, 3, 0], &[true, true, true, false, false]);
        test_selectors(&[1, 3, 0, 2], &[false, true, false, true, true]);
        test_selectors(&[1, 3, 2, 0], &[false, false, false, true, true]);
        test_selectors(&[2, 0, 1, 3], &[false, false, true, false, true]);
        test_selectors(&[2, 0, 3, 1], &[false, true, true, false, true]);
        test_selectors(&[2, 1, 0, 3], &[false, false, true, false, false]);
        test_selectors(&[2, 1, 3, 0], &[false, true, true, false, false]);
        test_selectors(&[2, 3, 0, 1], &[false, true, true, true, true]);
        test_selectors(&[2, 3, 1, 0], &[false, true, true, true, false]);
        test_selectors(&[3, 0, 1, 2], &[true, true, false, true, false]);
        test_selectors(&[3, 0, 2, 1], &[true, false, false, true, false]);
        test_selectors(&[3, 1, 0, 2], &[true, true, false, true, true]);
        test_selectors(&[3, 1, 2, 0], &[true, false, false, true, true]);
        test_selectors(&[3, 2, 0, 1], &[true, true, true, true, true]);
        test_selectors(&[3, 2, 1, 0], &[true, true, true, true, false]);
    }
}
