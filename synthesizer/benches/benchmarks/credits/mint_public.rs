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

use crate::{Benchmark, Operation};

use console::{
    network::Network,
    program::{Address, Literal, Plaintext, Value, Zero, U64},
};
use snarkvm_synthesizer::Program;
use snarkvm_utilities::TestRng;

use std::{marker::PhantomData, str::FromStr};

pub struct MintPublic<N: Network> {
    num_executions: usize,
    phantom: PhantomData<N>,
}

impl<N: Network> MintPublic<N> {
    pub fn new(num_executions: usize) -> Self {
        Self { num_executions, phantom: Default::default() }
    }
}

impl<N: Network> Benchmark<N> for MintPublic<N> {
    fn name(&self) -> String {
        format!("mint_public/{}_executions", self.num_executions)
    }

    fn setup_operations(&mut self) -> Vec<Vec<Operation<N>>> {
        // Construct the program.
        let program = Program::from_str(&format!(
            r"
program mint_public_{}.aleo;
mapping account:
    key left as address.public;
    value right as u64.public;
function mint_public:
    input r0 as address.public;
    input r1 as u64.public;
    finalize r0 r1;
finalize mint_public:
    input r0 as address.public;
    input r1 as u64.public;
    get.or_init account[r0] 0u64 into r2;
    add r2 r1 into r3;
    set r3 into account[r0];
",
            self.num_executions
        ))
        .unwrap();
        vec![vec![Operation::Deploy(Box::new(program))]]
    }

    fn benchmark_operations(&mut self) -> Vec<Operation<N>> {
        // Initialize storage for the benchmark operations.
        let mut benchmarks = Vec::with_capacity(self.num_executions);
        // Initialize an RNG for generating the operations.
        let rng = &mut TestRng::default();
        // Construct the operations.
        for _ in 0..self.num_executions {
            benchmarks.push(Operation::Execute(
                format!("mint_public_{}.aleo", self.num_executions),
                "mint_public".to_string(),
                vec![
                    Value::Plaintext(Plaintext::from(Literal::Address(
                        #[allow(deprecated)]
                        Address::rand(rng),
                    ))),
                    Value::Plaintext(Plaintext::from(Literal::U64(U64::zero()))),
                ],
            ));
        }
        benchmarks
    }
}
