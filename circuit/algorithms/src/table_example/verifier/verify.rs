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

use crate::Verify;

impl<E: Environment> Verify for TableExampleVerifier<E> {
    type Input = Field<E>;
    type Output = Boolean<E>;

    fn verify(&self, input: &[Self::Input]) -> Self::Output {
        // TODO: set the table, for both Console and Circuit, during Self::new(..)
        let input = input.to_vec();
        let key_0 = &input[0];
        let lc_0: LinearCombination<E::BaseField> = key_0.clone().into();
        let key_1 = &input[1];
        let lc_1: LinearCombination<E::BaseField> = key_1.clone().into();
        let value = &input[2];
        let lc_2: LinearCombination<E::BaseField> = value.clone().into();
        let table_index = 0usize;
        let num_lookups = 10;
        let mut lookup_table = LookupTable::default();
        for _ in 0..num_lookups {
            let lookup_value = [lc_0.value(), lc_1.value()];
            lookup_table.fill(lookup_value, lc_2.value());
        }
        E::add_lookup_table(lookup_table);

        for _ in 0..num_lookups {
            E::enforce_lookup(|| (key_0, key_1, value, table_index));
        }

        Boolean::<E>::from_str("true").unwrap()
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::{assert_scope_with_lookup, Circuit};
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

        // Initialize the native TableExample verifier.
        let rng = &mut TestRng::default();
        let input = (0..3).map(|_| Uniform::rand(rng)).collect::<Vec<_>>();
        let native =
            console::table_example::verifier::TableExampleVerifier::<<Circuit as Environment>::Network>::setup(&input)?;

        // Initialize the circuit TableExample verifier.
        let primitive = console::TableExample::<<Circuit as Environment>::Network>::setup(&input)?;
        let circuit = TableExampleVerifier::<Circuit>::new(Mode::Constant, primitive);

        // Compute the expected verification.
        let expected = native.verify(&input).expect("Failed to verify native input");
        // Prepare the circuit input.
        let circuit_input: Vec<Field<_>> = Inject::new(mode, input);

        Circuit::scope(format!("TableExample {mode}"), || {
            let candidate = circuit.verify(&circuit_input);
            assert_scope_with_lookup!(num_constants, num_public, num_private, num_constraints, num_lookup_constraints);
            assert_eq!(expected, candidate.eject_value());
        });
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
