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

use crate::{BenchmarkOperations, Operation, SetupOperations, Workload};

use console::network::Network;
use snarkvm_synthesizer::Program;

use std::{marker::PhantomData, str::FromStr};

pub struct StaticGet<N: Network> {
    num_mappings: usize,
    num_commands: usize,
    num_executions: usize,
    num_programs: usize,
    phantom: PhantomData<N>,
}

impl<N: Network> StaticGet<N> {
    pub fn new(num_mappings: usize, num_commands: usize, num_executions: usize, num_programs: usize) -> Self {
        Self { num_mappings, num_commands, num_executions, num_programs, phantom: Default::default() }
    }
}

impl<N: Network> Workload<N> for StaticGet<N> {
    fn name(&self) -> String {
        format!(
            "static_get/{}_mappings/{}_commands/{}_executions/{}_programs",
            self.num_mappings, self.num_commands, self.num_executions, self.num_programs
        )
    }

    fn init(&mut self) -> (SetupOperations<N>, BenchmarkOperations<N>) {
        // Initialize storage for the setup operations.
        let mut deploy_operations = Vec::with_capacity(self.num_programs);
        let mut init_operations = Vec::with_capacity(self.num_programs);
        // Construct the operations.
        for i in 0..self.num_programs {
            // Initialize the program string.
            let mut program_string =
                format!("program get_{}_{}_{}_{i}.aleo;", self.num_mappings, self.num_commands, self.num_executions);
            // Add the mappings.
            for j in 0..self.num_mappings {
                program_string
                    .push_str(&format!("mapping map_{j}:key left as field.public;value right as field.public;"));
            }
            // Construct the init function.
            let mut init_function = "function init:finalize;finalize init:".to_string();
            // Construct the getter function.
            let mut getter_function = "function getter:finalize;finalize getter:".to_string();
            // Add the commands.
            for j in 0..self.num_mappings {
                for k in 0..self.num_commands {
                    init_function.push_str(&format!("set {k}field into map_{j}[{k}field];"));
                    getter_function.push_str(&format!("get map_{j}[{k}field] into r{k};"));
                }
            }
            // Add the functions to the program string.
            program_string.push_str(&init_function);
            program_string.push_str(&getter_function);
            // Construct and add the setup operations.
            deploy_operations.push(Operation::Deploy(Box::new(Program::from_str(&program_string).unwrap())));
            init_operations.push(Operation::Execute(
                format!("get_{}_{}_{}_{i}.aleo", self.num_mappings, self.num_commands, self.num_executions),
                "init".to_string(),
                vec![],
            ));
        }
        let setups = vec![deploy_operations, init_operations];

        // Initialize storage for the benchmark operations.
        let mut benchmarks = Vec::with_capacity(self.num_programs * self.num_executions);
        // Construct the operations.
        for i in 0..self.num_programs {
            for _ in 0..self.num_executions {
                benchmarks.push(Operation::Execute(
                    format!("get_{}_{}_{}_{i}.aleo", self.num_mappings, self.num_commands, self.num_executions),
                    "getter".to_string(),
                    vec![],
                ));
            }
        }
        (setups, benchmarks)
    }
}
