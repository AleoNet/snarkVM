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

use console::{prelude::Network, program::Value};
use snarkvm_synthesizer::{Program, Transaction};

/// An operation executed in a workload.
#[derive(Clone, Debug)]
#[allow(unused)]
pub enum Operation<N: Network> {
    /// Deploy a program.
    Deploy(Box<Program<N>>),
    /// Execute a program.
    Execute(String, String, Vec<Value<N>>),
}

/// Batches of setup operations for the workload.
pub type SetupOperations<N> = Vec<Vec<Operation<N>>>;
/// Benchmark transactions for the workload.
pub type BenchmarkOperations<N> = Vec<Operation<N>>;

/// A trait for workloads.
pub trait Workload<N: Network> {
    /// The name of the workload.
    fn name(&self) -> String;
    /// Initialize the workload.
    fn init(&mut self) -> (SetupOperations<N>, BenchmarkOperations<N>);
}
