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

use crate::{Executable, Network, Record, RecordScheme};

use anyhow::{anyhow, Result};
use std::ops::Deref;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct Executables<N: Network>(Vec<Executable<N>>);

impl<N: Network> Executables<N> {
    /// Initializes a new instance of `Executables`.
    pub fn from(executables: Vec<Executable<N>>) -> Result<Self> {
        let mut padded_executables = executables.clone();
        while padded_executables.len() < N::NUM_EXECUTABLES {
            padded_executables.push(Executable::Noop);
        }

        let executables = Self(padded_executables);
        match executables.is_valid() {
            true => Ok(executables),
            false => Err(anyhow!("Failed to initialize the executables")),
        }
    }

    pub fn is_valid(&self) -> bool {
        // Ensure the number of executables is valid.
        if self.0.len() > N::NUM_EXECUTABLES {
            eprintln!("Incorrect number of executables: {}", self.0.len());
            return false;
        }

        // Ensure the number of inputs and outputs required is valid.
        let mut inputs = 0;
        let mut outputs = 0;

        for executable in &self.0 {
            // Fetch the execution type.
            let execution_type = match executable.execution_type() {
                Ok(execution_type) => execution_type,
                Err(error) => {
                    eprintln!("{}", error);
                    return false;
                }
            };

            // Tally the number of inputs and outputs required for this executable.
            inputs += execution_type.input_count() as usize;
            outputs += execution_type.output_count() as usize;
        }

        inputs <= N::NUM_INPUT_RECORDS && outputs <= N::NUM_OUTPUT_RECORDS && (inputs + outputs) <= N::NUM_TOTAL_RECORDS
    }

    pub fn verify_records(&self, input_records: &Vec<Record<N>>, output_records: &Vec<Record<N>>) -> bool {
        if !self.is_valid() {
            eprintln!("Executables is not well-formed");
            return false;
        }

        let mut num_inputs: usize = 0;
        let mut num_outputs: usize = 0;

        for executable in &self.0 {
            // Fetch the execution type.
            let execution_type = match executable.execution_type() {
                Ok(execution_type) => execution_type,
                Err(error) => {
                    eprintln!("{}", error);
                    return false;
                }
            };

            // Verify the input records have the correct program ID.
            for i in 0..execution_type.input_count() as usize {
                if input_records[num_inputs + i].program_id() != executable.program_id() {
                    eprintln!("Program ID in input record {} does not match executable", i);
                    return false;
                }
            }

            // Verify the output records have the correct program ID.
            for j in 0..execution_type.output_count() as usize {
                if output_records[num_outputs + j].program_id() != executable.program_id() {
                    eprintln!("Program ID in output record {} does not match executable", j);
                    return false;
                }
            }

            // Increment the number of inputs and outputs from this executable.
            num_inputs += execution_type.input_count() as usize;
            num_outputs += execution_type.output_count() as usize;
        }

        true
    }
}

impl<N: Network> Deref for Executables<N> {
    type Target = Vec<Executable<N>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
