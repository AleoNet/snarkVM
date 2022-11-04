// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use super::*;

impl<E: Environment, const RATE: usize> Hash for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Output = Field<E>;

    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        self.hash_many(input, 1).swap_remove(0)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;

    use anyhow::Result;

    const DOMAIN: &str = "PoseidonCircuit0";
    const ITERATIONS: usize = 10;
    const RATE: usize = 4;

    fn check_hash(
        mode: Mode,
        num_inputs: usize,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
        rng: &mut TestRng,
    ) -> Result<()> {
        use console::Hash as H;

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input = (0..num_inputs)
                .map(|_| console::Field::<<Circuit as Environment>::Network>::rand(rng))
                .collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = native.hash(&native_input).expect("Failed to hash native input");

            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = poseidon.hash(&input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_hash_constant() -> Result<()> {
        let mut rng = TestRng::default();

        for num_inputs in 0..=RATE {
            check_hash(Mode::Constant, num_inputs, 1, 0, 0, 0, &mut rng)?;
        }
        Ok(())
    }

    #[test]
    fn test_hash_public() -> Result<()> {
        let mut rng = TestRng::default();

        check_hash(Mode::Public, 0, 1, 0, 0, 0, &mut rng)?;
        check_hash(Mode::Public, 1, 1, 0, 335, 335, &mut rng)?;
        check_hash(Mode::Public, 2, 1, 0, 340, 340, &mut rng)?;
        check_hash(Mode::Public, 3, 1, 0, 345, 345, &mut rng)?;
        check_hash(Mode::Public, 4, 1, 0, 350, 350, &mut rng)?;
        check_hash(Mode::Public, 5, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 6, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 7, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 8, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 9, 1, 0, 1060, 1060, &mut rng)?;
        check_hash(Mode::Public, 10, 1, 0, 1060, 1060, &mut rng)
    }

    #[test]
    fn test_hash_private() -> Result<()> {
        let mut rng = TestRng::default();

        check_hash(Mode::Private, 0, 1, 0, 0, 0, &mut rng)?;
        check_hash(Mode::Private, 1, 1, 0, 335, 335, &mut rng)?;
        check_hash(Mode::Private, 2, 1, 0, 340, 340, &mut rng)?;
        check_hash(Mode::Private, 3, 1, 0, 345, 345, &mut rng)?;
        check_hash(Mode::Private, 4, 1, 0, 350, 350, &mut rng)?;
        check_hash(Mode::Private, 5, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 6, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 7, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 8, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 9, 1, 0, 1060, 1060, &mut rng)?;
        check_hash(Mode::Private, 10, 1, 0, 1060, 1060, &mut rng)
    }
}
