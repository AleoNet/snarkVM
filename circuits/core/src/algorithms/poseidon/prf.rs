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

impl<E: Environment> PseudorandomFunction for Poseidon<E> {
    type Input = Field<E>;
    type Output = Field<E>;
    type Seed = Field<E>;

    #[inline]
    fn prf(&self, seed: &Self::Seed, input: &[Self::Input]) -> Self::Output {
        // Construct the preimage: seed || length(input) || input.
        let mut preimage = Vec::with_capacity(2 + input.len());
        preimage.push(seed.clone());
        preimage.push(Field::constant((input.len() as u128).into())); // <- Input length *must* be constant.
        preimage.extend_from_slice(input);

        // Hash the preimage to derive the PRF output.
        self.hash(&preimage)
    }
}

impl<E: Environment> Count<dyn PseudorandomFunction<Seed = Field<E>, Input = Field<E>, Output = Field<E>>>
    for Poseidon<E>
{
    type Case = ();

    fn count(_parameter: &Self::Case) -> CircuitCount {
        todo!()
    }
}

impl<E: Environment> OutputMode<dyn PseudorandomFunction<Seed = Field<E>, Input = Field<E>, Output = Field<E>>>
    for Poseidon<E>
{
    type Case = ();

    fn output_mode(_input: &Self::Case) -> Mode {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{prf::PoseidonPRF as NativePoseidonPRF, PRF as NativePRF};
    use snarkvm_circuits_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;

    fn check_prf(
        mode: Mode,
        num_inputs: usize,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();
        let poseidon = Poseidon::new();

        for i in 0..ITERATIONS {
            // Prepare the seed.
            let native_seed = <Circuit as Environment>::BaseField::rand(rng);
            let seed = Field::new(mode, native_seed);

            // Prepare the preimage.
            let native_input =
                (0..num_inputs).map(|_| <Circuit as Environment>::BaseField::rand(rng)).collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = NativePoseidonPRF::<_, RATE, OPTIMIZED_FOR_WEIGHTS>::evaluate(&native_seed, &native_input);
            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon PRF {mode} {i}"), || {
                let candidate = poseidon.prf(&seed, &input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_prf_constant() {
        for num_inputs in 0..=RATE {
            check_prf(Mode::Constant, num_inputs, 1, 0, 0, 0);
        }
    }

    #[test]
    fn test_prf_public() {
        check_prf(Mode::Public, 0, 1, 0, 335, 335);
        check_prf(Mode::Public, 1, 1, 0, 340, 340);
        check_prf(Mode::Public, 2, 1, 0, 345, 345);
        check_prf(Mode::Public, 3, 1, 0, 700, 700);
        check_prf(Mode::Public, 4, 1, 0, 700, 700);
        check_prf(Mode::Public, 5, 1, 0, 700, 700);
        check_prf(Mode::Public, 6, 1, 0, 700, 700);
        check_prf(Mode::Public, 7, 1, 0, 1055, 1055);
        check_prf(Mode::Public, 8, 1, 0, 1055, 1055);
        check_prf(Mode::Public, 9, 1, 0, 1055, 1055);
        check_prf(Mode::Public, 10, 1, 0, 1055, 1055);
    }

    #[test]
    fn test_prf_private() {
        check_prf(Mode::Private, 0, 1, 0, 335, 335);
        check_prf(Mode::Private, 1, 1, 0, 340, 340);
        check_prf(Mode::Private, 2, 1, 0, 345, 345);
        check_prf(Mode::Private, 3, 1, 0, 700, 700);
        check_prf(Mode::Private, 4, 1, 0, 700, 700);
        check_prf(Mode::Private, 5, 1, 0, 700, 700);
        check_prf(Mode::Private, 6, 1, 0, 700, 700);
        check_prf(Mode::Private, 7, 1, 0, 1055, 1055);
        check_prf(Mode::Private, 8, 1, 0, 1055, 1055);
        check_prf(Mode::Private, 9, 1, 0, 1055, 1055);
        check_prf(Mode::Private, 10, 1, 0, 1055, 1055);
    }
}
