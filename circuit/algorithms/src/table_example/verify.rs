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

use super::*;

impl<E: Environment> Verify for TableExample<E> {
    // type Input = Boolean<E>;
    type Input = Field<E>;
    type Output = Boolean<E>;

    fn verify(&self, input: &[Self::Input]) -> Self::Output {
        self.verifier.verify(&input)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};
    use snarkvm_utilities::{TestRng, Uniform};

    use anyhow::Result;

    fn check_verify(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
        num_lookup_constraints: u64,
    ) -> Result<()> {
        use console::Verify as H;

        // Initialize TableExample.
        let rng = &mut TestRng::default();
        let input = (0..3).map(|_| Uniform::rand(rng)).collect::<Vec<_>>();
        let native = console::TableExample::<<Circuit as Environment>::Network>::setup(&input)?;
        let circuit = TableExample::<Circuit>::new(Mode::Constant, native.clone());

        // Compute the expected hash.
        let expected = native.verify(&input).expect("Failed to hash native input");
        // Prepare the circuit input.
        let circuit_input: Vec<Field<_>> = Inject::new(mode, input);

        Circuit::scope(format!("TableExample {mode}"), || {
            // Perform the hash operation.
            let candidate = circuit.verify(&circuit_input);
            assert_scope_with_lookup!(num_constants, num_public, num_private, num_constraints, num_lookup_constraints);
            assert_eq!(expected, candidate.eject_value());
        });
        Circuit::reset();
        Ok(())
    }

    #[test]
    fn test_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 1, 0, 0, 0, 10)
    }

    #[test]
    fn test_verify_public() -> Result<()> {
        check_verify(Mode::Public, 1, 0, 0, 0, 10)
    }

    #[test]
    fn test_verify_private() -> Result<()> {
        check_verify(Mode::Private, 1, 0, 0, 0, 10)
    }
}
