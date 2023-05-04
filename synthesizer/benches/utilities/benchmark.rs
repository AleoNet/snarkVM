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

use crate::utilities::{initialize_vm, ObjectStore, split};

use console::{network::Testnet3, prelude::Network, program::Value};
use snarkvm_synthesizer::{Program, Transaction};

use itertools::Itertools;
use std::{collections::hash_map::DefaultHasher, hash::Hash, iter, path::PathBuf};
use console::account::PrivateKey;
use snarkvm_synthesizer::helpers::memory::ConsensusMemory;
use snarkvm_utilities::TestRng;

/// An operation executed in a benchmark.
#[derive(Clone, Debug)]
#[allow(unused)]
pub enum Operation<N: Network> {
    /// Deploy a program.
    Deploy(Box<Program<N>>),
    /// Execute a program.
    Execute(String, String, Vec<Value<N>>),
}

impl<N: Network> Operation<N> {
    /// Returns a unique identifier for the operation.
    pub fn uid(&self) -> String {
        let string = match self {
            Operation::Deploy(program) => format!("deploy({})", program),
            Operation::Execute(program, function, values) => {
                format!("execute({}, {}, {})", program, function, values.join(","))
            }
        };
        string.hash(&mut DefaultHasher::new()).to_string()
    }
}

/// A trait for benchmarks.
pub trait Benchmark<N: Network> {
    /// The name of the benchmark.
    fn name(&self) -> String;
    /// Batches of operations to be run to setup the benchmark.
    fn setup_operations(&mut self) -> Vec<Vec<Operation<N>>>;
    /// Operations to be run for the benchmark.
    fn benchmark_operations(&mut self) -> Vec<Operation<N>>;
}
