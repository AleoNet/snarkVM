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

pub mod credits;
pub use credits::*;

pub mod get;
pub use get::*;

pub mod get_or_init;
pub use get_or_init::*;

pub mod set;
pub use set::*;

use crate::utilities::{Operation, Workload};

use console::prelude::Network;

use itertools::Itertools;
use std::iter;

type Setups<N> = Vec<Vec<Operation<N>>>;
type Benchmarks<N> = Vec<(String, Vec<Operation<N>>)>;

/// A helper function for preparing benchmarks.
/// This function takes a number of workloads and returns the setup operations and the benchmarks.
/// Note that setup operations are aggregated across all workloads.
pub fn prepare_benchmarks<N: Network>(workloads: Vec<Box<dyn Workload<N>>>) -> (Setups<N>, Benchmarks<N>) {
    let mut setup_operations = vec![];
    let mut benchmarks = vec![];
    for mut workload in workloads {
        setup_operations.push(workload.setup());
        benchmarks.push((workload.name(), workload.run()));
    }

    // Aggregate the batches for each setup operation.
    let max_num_batches = setup_operations.iter().map(|operations| operations.len()).max().unwrap_or(0);
    let mut batches = iter::repeat_with(Vec::new).take(max_num_batches).collect_vec();
    for setup in setup_operations {
        for (i, batch) in setup.into_iter().enumerate() {
            batches[i].extend(batch);
        }
    }

    (batches, benchmarks)
}
