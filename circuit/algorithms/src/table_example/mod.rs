// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod verifier;
use verifier::TableExampleVerifier;

mod verify;

#[cfg(all(test, console))]
use snarkvm_circuit_types::environment::assert_scope_with_lookup;

use crate::Verify;
use snarkvm_circuit_types::prelude::*;

pub struct TableExample<E: Environment> {
    /// The internal TableExample verifier used to process one iteration.
    verifier: TableExampleVerifier<E>,
}

#[cfg(console)]
impl<E: Environment> Inject for TableExample<E> {
    type Primitive = console::TableExample<E::Network>;

    /// Initializes a new instance of a TableExample circuit with the given TableExample variant.
    fn new(_mode: Mode, table_example: Self::Primitive) -> Self {
        // Initialize the TableExample verifier.
        let verifier = TableExampleVerifier::<E>::constant(table_example);

        Self { verifier }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{TestRng, Uniform};

    use anyhow::Result;

    const ITERATIONS: usize = 10;

    #[test]
    fn test_setup_constant() -> Result<()> {
        for _ in 0..ITERATIONS {
            let rng = &mut TestRng::default();
            let input = (0..3).map(|_| Uniform::rand(rng)).collect::<Vec<_>>();
            let native = console::TableExample::<<Circuit as Environment>::Network>::setup(&input)?;
            let circuit = TableExample::<Circuit>::new(Mode::Constant, native.clone());
            // TODO: fix test
            // println!("circuit.verifier.tables(): {:?}", circuit.verifier.tables());
            // assert!(circuit.verifier.tables().len() > 0);
        }
        Ok(())
    }
}
