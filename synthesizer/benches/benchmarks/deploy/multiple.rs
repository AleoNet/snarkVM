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

use crate::{construct_program, Benchmark, Operation};

use console::network::Network;

use std::marker::PhantomData;

pub struct DeployMultiple<N: Network> {
    num_mappings: usize,
    num_deployments: usize,
    phantom: PhantomData<N>,
}

impl<N: Network> DeployMultiple<N> {
    pub fn new(num_mappings: usize, num_deployments: usize) -> Self {
        Self { num_mappings, num_deployments, phantom: Default::default() }
    }
}

impl<N: Network> Benchmark<N> for DeployMultiple<N> {
    fn name(&self) -> String {
        format!("deploy_multiple/{}_mappings/{}_deployments", self.num_mappings, self.num_deployments)
    }

    fn setup_operations(&mut self) -> Vec<Vec<Operation<N>>> {
        vec![vec![]]
    }

    fn benchmark_operations(&mut self) -> Vec<Operation<N>> {
        (0..self.num_deployments)
            .map(|i| Operation::Deploy(Box::new(construct_program(i, self.num_mappings))))
            .collect::<Vec<_>>()
    }
}
