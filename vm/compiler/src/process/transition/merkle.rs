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

/// The depth of the Merkle tree for the transition.
const TRANSITION_DEPTH: u8 = 4;

/// The Merkle tree for the transition.
type TransitionTree<N> = BHPMerkleTree<N, TRANSITION_DEPTH>;
/// The Merkle path for an input or output ID in the transition.
pub type TransitionPath<N> = MerklePath<N, TRANSITION_DEPTH>;

impl<N: Network> Transition<N> {
    /// Returns the transition root, by computing the root for a Merkle tree of the input and output IDs.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns the Merkle leaf for the given input or output ID in the transition.
    pub fn to_leaf(&self, id: &Field<N>, is_input: bool) -> Result<TransitionLeaf<N>> {
        // Set the version.
        let version = 0u8;
        // Match on the input or output ID.
        match is_input {
            true => {
                // Iterate through the transition inputs.
                for (index, input) in self.inputs.iter().enumerate() {
                    // Check if the input ID matches the given ID.
                    if id == input.id() {
                        // Return the transition leaf.
                        return Ok(TransitionLeaf::new(
                            version,
                            index as u8,
                            self.program_id,
                            self.function_name,
                            input.variant(),
                            *id,
                        ));
                    }
                }
                // Error if the input ID was not found.
                bail!("Input ID not found in transition")
            }
            false => {
                // Iterate through the transition outputs.
                for (index, output) in self.outputs.iter().enumerate() {
                    // Check if the output ID matches the given ID.
                    if id == output.id() {
                        // Compute the output index.
                        let output_index = (self.inputs.len() + index) as u8;
                        // Return the transition leaf.
                        return Ok(TransitionLeaf::new(
                            version,
                            output_index,
                            self.program_id,
                            self.function_name,
                            output.variant(),
                            *id,
                        ));
                    }
                }
                // Error if the output ID was not found.
                bail!("Output ID not found in transition")
            }
        }
    }

    /// Returns the Merkle path for the transition leaf.
    pub fn to_path(&self, leaf: &TransitionLeaf<N>) -> Result<TransitionPath<N>> {
        // Compute the Merkle path.
        self.to_tree()?.prove(leaf.index() as usize, &leaf.to_bits_le())
    }

    /// The Merkle tree of input and output IDs for the transition.
    pub fn to_tree(&self) -> Result<TransitionTree<N>> {
        Self::function_tree(&self.program_id, &self.function_name, &self.inputs, &self.outputs)
    }

    /// Returns the Merkle tree for the given program ID, function name, inputs, and outputs.
    pub(super) fn function_tree(
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        inputs: &[Input<N>],
        outputs: &[Output<N>],
    ) -> Result<TransitionTree<N>> {
        // Ensure the number of inputs is within the allowed range.
        ensure!(
            inputs.len() <= N::MAX_INPUTS,
            "Transition cannot exceed {} inputs, found {} inputs",
            N::MAX_INPUTS,
            inputs.len()
        );
        // Ensure the number of outputs is within the allowed range.
        ensure!(
            outputs.len() <= N::MAX_OUTPUTS,
            "Transition cannot exceed {} outputs, found {} outputs",
            N::MAX_OUTPUTS,
            outputs.len()
        );

        // Set the version.
        let version = 0u8;
        // Prepare the input leaves.
        let input_leaves = inputs.iter().enumerate().map(|(index, input)| {
            // Construct each leaf as (version || index || program ID || function name || variant || ID).
            TransitionLeaf::new(version, index as u8, *program_id, *function_name, input.variant(), *input.id())
                .to_bits_le()
        });
        // Prepare the output leaves.
        let output_leaves = outputs.iter().enumerate().map(|(index, output)| {
            // Construct each leaf as (version || index || program ID || function name || variant || ID).
            TransitionLeaf::new(
                version,
                (inputs.len() + index) as u8,
                *program_id,
                *function_name,
                output.variant(),
                *output.id(),
            )
            .to_bits_le()
        });
        // Compute the function tree.
        N::merkle_tree_bhp::<TRANSITION_DEPTH>(&input_leaves.chain(output_leaves).collect::<Vec<_>>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_transition_depth() {
        // Ensure the log2 relationship between depth and the maximum number of transition inputs & outputs.
        assert_eq!(2usize.pow(TRANSITION_DEPTH as u32), CurrentNetwork::MAX_INPUTS + CurrentNetwork::MAX_OUTPUTS);
    }
}
