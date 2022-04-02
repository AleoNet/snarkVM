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

use snarkvm_circuits_types::{Boolean, Environment, Field, Group, Neg, Ternary};

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHPCRH<E, NUM_WINDOWS, WINDOW_SIZE> {
    pub fn hash(&self, input: &[Boolean<E>]) -> Field<E> {
        self.hash_bits_inner(input).to_x_coordinate()
    }

    fn hash_bits_inner(&self, input: &[Boolean<E>]) -> Group<E> {
        let constant_false = Boolean::<E>::constant(false);

        // Ensure the input size is within the parameter size,
        if input.len() > NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE {
            E::halt("Incorrect input length")
        }

        // Pad the input to a multiple of `BHP_CHUNK_SIZE` for hashing.
        let mut input = input.to_vec();
        if input.len() % BHP_CHUNK_SIZE != 0 {
            let padding = BHP_CHUNK_SIZE - (input.len() % BHP_CHUNK_SIZE);
            input.extend_from_slice(&vec![constant_false; BHP_CHUNK_SIZE][..padding]);
            assert_eq!(input.len() % BHP_CHUNK_SIZE, 0);
        }

        // Compute sum of h_i^{sum of (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment}
        // for all i. Described in section 5.4.1.7 in the Zcash protocol specification.
        //
        // Note: `.zip()` is used here (as opposed to `.zip_eq()`) as the input can be less than
        // `NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE` in length, which is the parameter size here.
        let zero = Field::<E>::zero();
        input
            .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
            .zip(self.bases.iter())
            .flat_map(|(bits, bases)| {
                bits.chunks(BHP_CHUNK_SIZE).zip(bases).map(|(chunk_bits, base)| {
                    let mut x_coeffs = vec![];
                    let mut y_coeffs = vec![];
                    let mut base_power = base.clone();
                    for _ in 0..4 {
                        x_coeffs.push(base_power.to_x_coordinate());
                        y_coeffs.push(base_power.to_y_coordinate());
                        base_power += base;
                    }

                    let precomp = &chunk_bits[0] & &chunk_bits[1];
                    let mut x = Field::<E>::zero();
                    x += &x_coeffs[0];
                    x += Field::ternary(&chunk_bits[0], &(&x_coeffs[1] - &x_coeffs[0]), &zero);
                    x += Field::ternary(&chunk_bits[1], &(&x_coeffs[2] - &x_coeffs[0]), &zero);
                    x += Field::ternary(&precomp, &(&x_coeffs[3] - &x_coeffs[2] - &x_coeffs[1] + &x_coeffs[0]), &zero);

                    // Three bit conditional neg lookup for Y
                    let y = Field::ternary(
                        &chunk_bits[0],
                        &Field::ternary(&chunk_bits[1], &y_coeffs[3], &y_coeffs[1]),
                        &Field::ternary(&chunk_bits[1], &y_coeffs[2], &y_coeffs[0]),
                    );

                    let y = Field::ternary(&chunk_bits[2], &y.clone().neg(), &y);

                    Group::from_xy_coordinates(x, y)
                })
            })
            .fold(Group::zero(), |acc, x| acc + x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::BHPCRH as NativeBHP, CRH};
    use snarkvm_circuits_environment::{Circuit, Mode};
    use snarkvm_circuits_types::Eject;
    use snarkvm_curves::edwards_bls12::EdwardsProjective;

    use snarkvm_utilities::{test_rng, ToBits, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "bhp_gadget_setup_test";

    fn check_hash(mode: Mode) {
        let rng = &mut test_rng();
        let bits = (0..1)
            .map(|_| <Circuit as Environment>::BaseField::rand(rng))
            .collect::<Vec<_>>()
            .iter()
            .flat_map(|el| el.to_bits_le())
            .collect::<Vec<_>>();
        let native_hasher = NativeBHP::<EdwardsProjective, 59, 63>::setup(MESSAGE);
        let circuit_hasher = BHPCRH::<Circuit, 59, 63>::setup(MESSAGE);

        for i in 0..ITERATIONS {
            let native_hash = native_hasher.hash(&bits).unwrap();
            let circuit_input = bits.iter().map(|b| Boolean::<_>::new(mode, *b)).collect::<Vec<Boolean<_>>>();

            Circuit::scope(format!("BHP {mode} {i}"), || {
                let circuit_hash = circuit_hasher.hash(&circuit_input).eject_value();
                assert_eq!(native_hash, circuit_hash);
            });
        }
    }

    #[test]
    fn test_hash_constant() {
        check_hash(Mode::Constant);
    }

    #[test]
    fn test_hash_public() {
        check_hash(Mode::Public);
    }

    #[test]
    fn test_hash_private() {
        check_hash(Mode::Private);
    }
}
