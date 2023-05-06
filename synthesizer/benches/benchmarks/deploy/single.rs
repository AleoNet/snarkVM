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

pub struct DeploySingle<N: Network> {
    num_mappings: usize,
    phantom: PhantomData<N>,
}

impl<N: Network> DeploySingle<N> {
    pub fn new(num_mappings: usize) -> Self {
        Self { num_mappings, phantom: Default::default() }
    }
}

impl<N: Network> Benchmark<N> for DeploySingle<N> {
    fn name(&self) -> String {
        format!("deploy_single/{}_mappings", self.num_mappings)
    }

    fn setup_operations(&mut self) -> Vec<Vec<Operation<N>>> {
        vec![vec![]]
    }

    fn benchmark_operations(&mut self) -> Vec<Operation<N>> {
        vec![Operation::Deploy(Box::new(construct_program(0, self.num_mappings)))]
    }
}
