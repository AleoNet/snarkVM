// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::prelude::*;
use snarkvm_utilities::ToBytes;

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::sync::Arc;

#[derive(Clone)]
pub struct State<C: Parameters> {
    inputs: Vec<Input<C>>,
    outputs: Vec<Output<C>>,
}

impl<C: Parameters> State<C> {
    /// Returns a new instance of `StateBuilder`.
    pub fn builder() -> StateBuilder<C> {
        StateBuilder::new()
    }
}

#[derive(Clone)]
pub struct StateBuilder<C: Parameters> {
    inputs: Vec<Input<C>>,
    outputs: Vec<Output<C>>,
    joint_serial_numbers: Vec<u8>,
    errors: Vec<String>,
}

impl<C: Parameters> StateBuilder<C> {
    /// Initializes a new instance of `StateBuilder`.
    pub fn new() -> Self {
        Self {
            inputs: Vec::new(),
            outputs: Vec::new(),
            joint_serial_numbers: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Adds the given input into the builder.
    pub fn add_input(mut self, input: Input<C>) -> Self {
        // Ensure there are no outputs assigned yet, as the builder computes joint serial numbers.
        if !self.outputs.is_empty() {
            self.errors.push("Builder cannot add new inputs after outputs".into());
        }

        match self.inputs.len() < C::NUM_INPUT_RECORDS {
            true => self.inputs.push(input),
            false => self.errors.push("Builder exceeded maximum inputs".into()),
        };
        self
    }

    /// Adds the given output into the builder.
    pub fn add_output(mut self, output: Output<C>) -> Self {
        match self.outputs.len() < C::NUM_OUTPUT_RECORDS {
            true => self.outputs.push(output),
            false => self.errors.push("Builder exceeded maximum outputs".into()),
        };
        self
    }

    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    /// Finalizes the builder and returns a new instance of `State`.
    pub fn build<R: Rng + CryptoRng>(&mut self, noop: Arc<NoopProgram<C>>, rng: &mut R) -> Result<State<C>> {
        // Ensure there are no errors in the build process yet.
        if !self.errors.is_empty() {
            for error in &self.errors {
                eprintln!("{}", error);
            }
            return Err(anyhow!("State builder encountered build errors: {:?}", self.errors));
        }

        // Construct the inputs.
        let mut inputs = self.inputs.clone();
        // Pad the inputs with noop inputs if necessary.
        while inputs.len() < C::NUM_INPUT_RECORDS {
            // TODO (howardwu): Decide whether to "push" or "push_front" for program flow.
            inputs.push(Input::new_noop(noop.clone(), rng)?);
        }

        // Update the joint serial numbers.
        self.update_joint_serial_numbers()?;

        // Construct the outputs.
        let mut outputs = self.outputs.clone();
        // Pad the outputs with noop outputs if necessary.
        while outputs.len() < C::NUM_OUTPUT_RECORDS {
            let position = (C::NUM_INPUT_RECORDS + outputs.len()) as u8;
            // TODO (howardwu): Decide whether to "push" or "push_front" for program flow.
            outputs.push(Output::new_noop(noop.clone(), position, rng)?);
        }

        Ok(State { inputs, outputs })
    }

    fn update_joint_serial_numbers(&mut self) -> Result<()> {
        // Compute the joint serial numbers.
        let mut joint_serial_numbers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        for input in self.inputs.iter().take(C::NUM_INPUT_RECORDS) {
            joint_serial_numbers.extend_from_slice(&input.serial_number().to_bytes_le()?);
        }
        self.joint_serial_numbers = joint_serial_numbers;
        Ok(())
    }
}
