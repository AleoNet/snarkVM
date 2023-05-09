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
use snarkvm_synthesizer::Program;

use std::{marker::PhantomData, str::FromStr};

/// A dummy benchmark that does nothing.
/// This pattern can be used to perform one-off initializations of the VM for a particular workload.
pub struct Dummy<N: Network> {
    name: String,
    phantom: PhantomData<N>,
}

impl<N: Network> Dummy<N> {
    pub fn new(name: String) -> Self {
        Self { name, phantom: Default::default() }
    }
}

impl<N: Network> Benchmark<N> for Dummy<N> {
    fn name(&self) -> String {
        format!("dummy_{}", self.name)
    }

    fn setup_operations(&mut self) -> Vec<Vec<Operation<N>>> {
        vec![vec![Operation::Deploy(Box::new(
            Program::from_str(&format!("program {}.aleo;function foo:", &self.name())).unwrap(),
        ))]]
    }

    fn benchmark_operations(&mut self) -> Vec<Operation<N>> {
        vec![]
    }
}
