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

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> HashUncompressed
    for BHP<E, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = Boolean<E>;
    type Output = Group<E>;

    /// Returns the BHP hash of the given input as an affine group element.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Self::Output {
        // Ensure the input size is at least the window size.
        if input.len() <= WINDOW_SIZE * BHP_CHUNK_SIZE {
            E::halt(format!("Inputs to this BHP variant must be greater than {} bits", WINDOW_SIZE * BHP_CHUNK_SIZE))
        }

        // Ensure the input size is within the parameter size.
        let mut input = input.to_vec();
        match input.len() <= NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE {
            true => {
                // Pad the input to a multiple of `BHP_CHUNK_SIZE` for hashing.
                if input.len() % BHP_CHUNK_SIZE != 0 {
                    let padding = BHP_CHUNK_SIZE - (input.len() % BHP_CHUNK_SIZE);
                    input.resize(input.len() + padding, Boolean::constant(false));
                    assert_eq!(input.len() % BHP_CHUNK_SIZE, 0);
                }
            }
            false => E::halt(format!(
                "Inputs to this BHP variant cannot exceed {} bits",
                NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE
            )),
        }

        // Declare the 1/2 constant field element.
        let one_half = Field::constant(E::BaseField::half());

        // Declare the constant coefficients A and B for the Montgomery curve.
        let coeff_a = Field::constant(<E::AffineParameters as TwistedEdwardsParameters>::MontgomeryParameters::COEFF_A);
        let coeff_b = Field::constant(<E::AffineParameters as TwistedEdwardsParameters>::MontgomeryParameters::COEFF_B);

        // Implements the incomplete addition formulae of two Montgomery curve points.
        let montgomery_add = |(this_x, this_y): (&Field<E>, &Field<E>), (that_x, that_y): (&Field<E>, &Field<E>)| {
            // Construct `lambda` as a witness defined as:
            // `lambda := (that_y - this_y) / (that_x - this_x)`
            let lambda: Field<E> = witness!(|this_x, this_y, that_x, that_y| (that_y - this_y) / (that_x - this_x));

            // Ensure `lambda` is correct by enforcing:
            // `lambda * (that_x - this_x) == (that_y - this_y)`
            E::enforce(|| (&lambda, that_x - this_x, that_y - this_y));

            // Construct `sum_x` as a witness defined as:
            // `sum_x := (B * lambda^2) - A - this_x - that_x`
            let sum_x: Field<E> = witness!(|lambda, that_x, this_x, coeff_a, coeff_b| {
                coeff_b * lambda.square() - coeff_a - this_x - that_x
            });

            // Ensure `sum_x` is correct by enforcing:
            // `(B * lambda) * lambda == (A + this_x + that_x + sum_x)`
            E::enforce(|| (&coeff_b * &lambda, &lambda, &coeff_a + this_x + that_x + &sum_x));

            // Construct `sum_y` as a witness defined as:
            // `sum_y := -(this_y + (lambda * (this_x - sum_x)))`
            let sum_y: Field<E> = witness!(|lambda, sum_x, this_x, this_y| -(this_y + (lambda * (sum_x - this_x))));

            // Ensure `sum_y` is correct by enforcing:
            // `(lambda * (this_x - sum_x)) == (this_y + sum_y)`
            E::enforce(|| (&lambda, this_x - &sum_x, this_y + &sum_y));

            (sum_x, sum_y)
        };

        // Compute sum of h_i^{sum of (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment}
        // for all i. Described in section 5.4.1.7 in the Zcash protocol specification.
        //
        // Note: `.zip()` is used here (as opposed to `.zip_eq()`) as the input can be less than
        // `NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE` in length, which is the parameter size here.
        input
            .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
            .zip(self.bases.iter())
            .map(|(bits, bases)| {
                // Initialize accumulating sum variables for the x- and y-coordinates.
                let mut sum_x = Field::zero();
                let mut sum_y = Field::zero();

                // One iteration costs 5 constraints.
                bits.chunks(BHP_CHUNK_SIZE).zip(bases).for_each(|(chunk_bits, base_lookups)| {
                    // Unzip the base lookups into `x_bases` and `y_bases`.
                    let (x_bases, y_bases) = base_lookups;

                    // Cast each input chunk bit as a field element.
                    let bit_0 = Field::from_boolean(&chunk_bits[0]);
                    let bit_1 = Field::from_boolean(&chunk_bits[1]);
                    let bit_2 = Field::from_boolean(&chunk_bits[2]);
                    let bit_0_and_1 = Field::from_boolean(&(&chunk_bits[0] & &chunk_bits[1])); // 1 constraint

                    // Compute the x-coordinate of the Montgomery curve point.
                    let montgomery_x: Field<E> = &x_bases[0]
                        + &bit_0 * (&x_bases[1] - &x_bases[0])
                        + &bit_1 * (&x_bases[2] - &x_bases[0])
                        + &bit_0_and_1 * (&x_bases[3] - &x_bases[2] - &x_bases[1] + &x_bases[0]);

                    // Compute the y-coordinate of the Montgomery curve point.
                    let montgomery_y = {
                        // Compute the y-coordinate of the Montgomery curve point, without any negation.
                        let y: Field<E> = &y_bases[0]
                            + bit_0 * (&y_bases[1] - &y_bases[0])
                            + bit_1 * (&y_bases[2] - &y_bases[0])
                            + bit_0_and_1 * (&y_bases[3] - &y_bases[2] - &y_bases[1] + &y_bases[0]);

                        // Determine the correct sign of the y-coordinate, as a witness.
                        //
                        // Instead of using `Field::ternary`, we create a witness & custom constraint to reduce
                        // the number of nonzero entries in the circuit, improving setup & proving time for Marlin.
                        let montgomery_y: Field<E> = witness!(|chunk_bits, y| if chunk_bits[2] { -y } else { y });

                        // Ensure the conditional negation of `witness_y` is correct as follows (1 constraint):
                        //     `(bit_2 - 1/2) * (-2 * y) == montgomery_y`
                        // which is equivalent to:
                        //     if `bit_2 == 0`, then `montgomery_y = -1/2 * -2 * y = y`
                        //     if `bit_2 == 1`, then `montgomery_y = 1/2 * -2 * y = -y`
                        E::enforce(|| (bit_2 - &one_half, -y.double(), &montgomery_y)); // 1 constraint

                        montgomery_y
                    };

                    // Sum the new Montgomery point into the accumulating sum.
                    (sum_x, sum_y) = montgomery_add((&sum_x, &sum_y), (&montgomery_x, &montgomery_y)); // 3 constraints
                });

                // Convert the accumulated sum into a point on the twisted Edwards curve.
                let edwards_x = &sum_x / sum_y; // 1 constraint
                let edwards_y = (&sum_x - Field::one()) / (sum_x + Field::one()); // 1 constraint
                Group::from_xy_coordinates(edwards_x, edwards_y) // 3 constraints
            })
            .fold(Group::zero(), |acc, group| acc + group) // 6 constraints
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

    fn check_hash_uncompressed<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Initialize the BHP hash.
        let native = NativeBHP::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        let circuit = BHP::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
        // Determine the number of inputs.
        let num_input_bits = NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE;

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
                assert_scope!(num_constants, num_public, num_private, num_constraints);
                assert_eq!(expected, candidate.eject_value());
            });
        }
    }

    #[test]
    fn test_hash_uncompressed_constant() {
        check_hash_uncompressed::<32, 48>(Mode::Constant, 6403, 0, 0, 0);
    }

    #[test]
    fn test_hash_uncompressed_public() {
        check_hash_uncompressed::<32, 48>(Mode::Public, 131, 0, 7997, 8029);
    }

    #[test]
    fn test_hash_uncompressed_private() {
        check_hash_uncompressed::<32, 48>(Mode::Private, 131, 0, 7997, 8029);
    }
}
