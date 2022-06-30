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

impl<E: Environment, const RATE: usize> PRF for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Output = Field<E>;
    type Seed = Field<E>;

    #[inline]
    fn prf(&self, seed: &Self::Seed, input: &[Self::Input]) -> Self::Output {
        // Construct the preimage: seed || input.
        let mut preimage = Vec::with_capacity(1 + input.len());
        preimage.push(seed.clone());
        preimage.extend_from_slice(input);

        // Hash the preimage to derive the PRF output.
        self.hash(&preimage)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, Uniform};

    use anyhow::Result;

    const DOMAIN: &str = "PoseidonCircuit0";
    const ITERATIONS: usize = 10;
    const RATE: usize = 4;

    fn check_prf(
        mode: Mode,
        num_inputs: usize,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        use console::PRF as P;

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        for i in 0..ITERATIONS {
            // Prepare the seed.
            let native_seed = Uniform::rand(&mut test_rng());
            let seed = Field::new(mode, native_seed);

            // Prepare the preimage.
            let native_input = (0..num_inputs).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = native.prf(&native_seed, &native_input).expect("Failed to PRF native input");

            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon PRF {mode} {i}"), || {
                let candidate = poseidon.prf(&seed, &input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_prf_constant() -> Result<()> {
        for num_inputs in 0..=RATE {
            check_prf(Mode::Constant, num_inputs, 1, 0, 0, 0)?;
        }
        Ok(())
    }

    #[test]
    fn test_prf_public() -> Result<()> {
        check_prf(Mode::Public, 0, 1, 0, 335, 335)?;
        check_prf(Mode::Public, 1, 1, 0, 340, 340)?;
        check_prf(Mode::Public, 2, 1, 0, 345, 345)?;
        check_prf(Mode::Public, 3, 1, 0, 350, 350)?;
        check_prf(Mode::Public, 4, 1, 0, 705, 705)?;
        check_prf(Mode::Public, 5, 1, 0, 705, 705)?;
        check_prf(Mode::Public, 6, 1, 0, 705, 705)?;
        check_prf(Mode::Public, 7, 1, 0, 705, 705)?;
        check_prf(Mode::Public, 8, 1, 0, 1060, 1060)?;
        check_prf(Mode::Public, 9, 1, 0, 1060, 1060)?;
        check_prf(Mode::Public, 10, 1, 0, 1060, 1060)
    }

    #[test]
    fn test_prf_private() -> Result<()> {
        check_prf(Mode::Private, 0, 1, 0, 335, 335)?;
        check_prf(Mode::Private, 1, 1, 0, 340, 340)?;
        check_prf(Mode::Private, 2, 1, 0, 345, 345)?;
        check_prf(Mode::Private, 3, 1, 0, 350, 350)?;
        check_prf(Mode::Private, 4, 1, 0, 705, 705)?;
        check_prf(Mode::Private, 5, 1, 0, 705, 705)?;
        check_prf(Mode::Private, 6, 1, 0, 705, 705)?;
        check_prf(Mode::Private, 7, 1, 0, 705, 705)?;
        check_prf(Mode::Private, 8, 1, 0, 1060, 1060)?;
        check_prf(Mode::Private, 9, 1, 0, 1060, 1060)?;
        check_prf(Mode::Private, 10, 1, 0, 1060, 1060)
    }
}
