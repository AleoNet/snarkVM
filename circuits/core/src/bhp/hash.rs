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

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHPCRH<E, NUM_WINDOWS, WINDOW_SIZE> {
    pub fn hash(&self, input: &[Boolean<E>]) -> Field<E> {
        self.hash_bits_inner(input).to_x_coordinate()
    }

    fn hash_bits_inner(&self, input: &[Boolean<E>]) -> Group<E> {
        // Ensure the input size is within the parameter size,
        if input.len() > NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE {
            E::halt("Incorrect input length")
        }

        // Pad the input to a multiple of `BHP_CHUNK_SIZE` for hashing.
        let mut input = input.to_vec();
        if input.len() % BHP_CHUNK_SIZE != 0 {
            let padding = BHP_CHUNK_SIZE - (input.len() % BHP_CHUNK_SIZE);
            input.extend_from_slice(&vec![Boolean::constant(false); BHP_CHUNK_SIZE][..padding]);
            assert_eq!(input.len() % BHP_CHUNK_SIZE, 0);
        }

        // Compute sum of h_i^{sum of (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment}
        // for all i. Described in section 5.4.1.7 in the Zcash protocol specification.
        //
        // Note: `.zip()` is used here (as opposed to `.zip_eq()`) as the input can be less than
        // `NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE` in length, which is the parameter size here.
        // let zero = Field::<E>::zero();
        // input
        //     .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
        //     .zip(self.bases.iter())
        //     .flat_map(|(bits, bases)| {
        //         bits.chunks(BHP_CHUNK_SIZE).zip(bases).map(|(chunk_bits, base)| {
        //             let mut x_coeffs = Vec::with_capacity(4);
        //             let mut y_coeffs = Vec::with_capacity(4);
        //             let mut acc_power = base.clone();
        //             for _ in 0..4 {
        //                 x_coeffs.push(acc_power.to_x_coordinate());
        //                 y_coeffs.push(acc_power.to_y_coordinate());
        //                 acc_power += base;
        //             }
        //
        //             let precomp = &chunk_bits[0] & &chunk_bits[1];
        //             let mut x = Field::<E>::zero();
        //             x += &x_coeffs[0];
        //             x += Field::ternary(&chunk_bits[0], &(&x_coeffs[1] - &x_coeffs[0]), &zero);
        //             x += Field::ternary(&chunk_bits[1], &(&x_coeffs[2] - &x_coeffs[0]), &zero);
        //             x += Field::ternary(&precomp, &(&x_coeffs[3] - &x_coeffs[2] - &x_coeffs[1] + &x_coeffs[0]), &zero);
        //
        //             // // Three bit conditional neg lookup for Y
        //             // let y = Field::ternary(
        //             //     &chunk_bits[0],
        //             //     &Field::ternary(&chunk_bits[1], &y_coeffs[3], &y_coeffs[1]),
        //             //     &Field::ternary(&chunk_bits[1], &y_coeffs[2], &y_coeffs[0]),
        //             // );
        //             //
        //             // let y = Field::ternary(&chunk_bits[2], &y.clone().neg(), &y);
        //
        //             Group::from_x_coordinate(x)
        //         })
        //     })
        //     .fold(Group::zero(), |acc, x| acc + x)

        input
            .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
            .zip(&self.bases)
            .flat_map(|(bits, bases)| {
                bits.chunks(BHP_CHUNK_SIZE).zip(bases).map(|(chunk_bits, base)| {
                    // base[(chunk_bits[0] as usize) | (chunk_bits[1] as usize) << 1 | (chunk_bits[2] as usize) << 2]
                    let mut encoded = base.clone();
                    if chunk_bits[0].eject_value() {
                        encoded += base;
                    }
                    if chunk_bits[1].eject_value() {
                        encoded += &base.double();
                    }
                    if chunk_bits[2].eject_value() {
                        encoded = -encoded;
                    }
                    encoded
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
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{test_rng, ToBits, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "BHPCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;

    fn check_hash<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(mode: Mode) {
        // Initialize the BHP hash.
        let native = NativeBHP::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = BHPCRH::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE;

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..num_input_bits).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
            // Compute the expected hash.
            let expected = native.hash(&input).expect("Failed to hash native input");
            // Prepare the circuit input.
            let circuit_input: Vec<Boolean<_>> = Inject::new(mode, input);

            Circuit::scope(format!("BHP {mode} {i}"), || {
                // Perform the hash operation.
                let candidate = circuit.hash(&circuit_input);
                assert_eq!(expected, candidate.eject_value());
            });
        }
    }

    #[test]
    fn test_hash_constant() {
        check_hash::<8, 32>(Mode::Constant);
    }

    #[test]
    fn test_hash_public() {
        check_hash::<8, 32>(Mode::Public);
    }

    #[test]
    fn test_hash_private() {
        check_hash::<8, 32>(Mode::Private);
    }
}
