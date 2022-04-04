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

use snarkvm_curves::{MontgomeryParameters, TwistedEdwardsParameters};

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
        input
            .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
            .zip(self.bases.iter())
            .map(|(bits, bases)| {
                let mut x_sum = Field::zero();
                let mut y_sum = Field::zero();

                bits.chunks(BHP_CHUNK_SIZE).zip(bases).for_each(|(chunk_bits, base)| {
                    // One iteration is 6 constraints.

                    let mut x_bases = Vec::with_capacity(4);
                    let mut y_bases = Vec::with_capacity(4);
                    let mut acc_power = base.clone();
                    for _ in 0..4 {
                        let x =
                            (Field::one() + acc_power.to_y_coordinate()) / (Field::one() - acc_power.to_y_coordinate());
                        let y = &x / acc_power.to_x_coordinate();

                        x_bases.push(x);
                        y_bases.push(y);
                        acc_power += base;
                    }

                    let bit_0 = Field::from_boolean(&chunk_bits[0]);
                    let bit_1 = Field::from_boolean(&chunk_bits[1]);
                    let bit_2 = Field::from_boolean(&chunk_bits[2]);
                    let bit_0_and_1 = Field::from_boolean(&(&chunk_bits[0] & &chunk_bits[1])); // 1 constraint

                    let montgomery_x: Field<E> = &x_bases[0]
                        + &bit_0 * (&x_bases[1] - &x_bases[0])
                        + &bit_1 * (&x_bases[2] - &x_bases[0])
                        + &bit_0_and_1 * (&x_bases[3] - &x_bases[2] - &x_bases[1] + &x_bases[0]);

                    let montgomery_y: Field<E> = witness!(|chunk_bits, y_bases| {
                        let y = match (chunk_bits[0], chunk_bits[1]) {
                            (false, false) => y_bases[0],
                            (false, true) => y_bases[2],
                            (true, false) => y_bases[1],
                            (true, true) => y_bases[3],
                        };
                        if chunk_bits[2] { -y } else { y }
                    });

                    // Conditional negation:
                    // We want to set the result to be a conditional negation of y_lc as follows:
                    // if b[2] == 0, result := y_lc
                    // if b[2] == 1, result := -y_lc
                    //
                    // We write this as follows:
                    // result = (b[2] - 1/2) * (-2 * y_lc);
                    //
                    // This works because
                    // * b[2] == 0 -> result = -1/2 * -2 * y_lc =  y_lc
                    // * b[2] == 1 -> result =  1/2 * -2 * y_lc = -y_lc
                    // We take this approach because it reduces the number of non-zero entries in
                    // the constraint, which makes it more efficient for Marlin.
                    {
                        let y_lc: Field<E> = &y_bases[0]
                            + bit_0 * (&y_bases[1] - &y_bases[0])
                            + bit_1 * (&y_bases[2] - &y_bases[0])
                            + bit_0_and_1 * (&y_bases[3] - &y_bases[2] - &y_bases[1] + &y_bases[0]);

                        E::enforce::<_, Field<E>, Field<E>, &Field<E>>(|| {
                            (bit_2 - Field::constant(E::BaseField::half()), -y_lc.double(), &montgomery_y)
                        }); // 1 constraint
                    }

                    {
                        let coeff_a = Field::constant(
                            <E::AffineParameters as TwistedEdwardsParameters>::MontgomeryParameters::COEFF_A,
                        );
                        let coeff_b = Field::constant(
                            <E::AffineParameters as TwistedEdwardsParameters>::MontgomeryParameters::COEFF_B,
                        );

                        let lambda = witness!(|montgomery_x, montgomery_y, x_sum, y_sum| {
                            (montgomery_y - y_sum) / (montgomery_x - x_sum)
                        });
                        E::assert_eq(&lambda * (&montgomery_x - &x_sum), &montgomery_y - &y_sum);

                        // Compute x'' = B*lambda^2 - A - x - x'
                        let xprime = witness!(|lambda, montgomery_x, x_sum, coeff_a, coeff_b| {
                            lambda.square() * coeff_b - coeff_a - x_sum - montgomery_x
                        });

                        let xprime_lc = &x_sum + &montgomery_x + &xprime + &coeff_a;

                        // (lambda) * (lambda) = (A + x + x' + x'')
                        let lambda_b = &lambda * &coeff_b;
                        E::assert_eq(lambda_b * &lambda, xprime_lc);

                        let yprime =
                            witness!(|lambda, xprime, x_sum, y_sum| { -(y_sum + (lambda * (xprime - x_sum))) });

                        E::assert_eq(lambda * (&x_sum - &xprime), &y_sum + &yprime);

                        x_sum = xprime;
                        y_sum = yprime;
                    }
                });

                let edwards_x = &x_sum / y_sum; // 2 constraints
                let edwards_y = (&x_sum - Field::one()) / (x_sum + Field::one()); // 2 constraints
                Group::from_xy_coordinates(edwards_x, edwards_y) // 3 constraints
            })
            .fold(Group::zero(), |acc, group| acc + group)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::BHPCRH as NativeBHP, CRH};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "BHPCircuit0";
    // const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;

    fn check_hash<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Initialize the BHP hash.
        let native = NativeBHP::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = BHPCRH::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE;
        // let num_input_bits = 128*8;

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

                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    // #[test]
    // fn test_hash_constant() {
    //     check_hash::<8, 32>(Mode::Constant);
    // }

    // #[test]
    // fn test_hash_public() {
    //     check_hash::<8, 32>(Mode::Public);
    // }

    #[test]
    fn test_hash_private() {
        check_hash::<32, 48>(Mode::Private, 41600, 0, 12669, 12701);
    }
}
