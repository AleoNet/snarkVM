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

impl<E: Environment> Group<E> {
    /// Returns the product of the group element and the cofactor.
    pub fn mul_by_cofactor(&self) -> Group<E> {
        // (For advanced users) The cofactor for this curve is `4`. Thus doubling is used to be performant.
        // See unit tests below, which sanity check that this condition holds.
        debug_assert!(E::Affine::cofactor().len() == 1 && E::Affine::cofactor()[0] == 4);

        self.double().double()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 250;

    fn check_mul_by_cofactor(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());

            // Multiply the point by the inverse of the cofactor.
            let input = expected.div_by_cofactor();
            assert_eq!(expected, input.mul_by_cofactor());

            // Initialize the input.
            let affine = Group::<Circuit>::new(mode, input);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = affine.mul_by_cofactor();
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_mul_by_cofactor_constant() {
        check_mul_by_cofactor(Mode::Constant, 6, 0, 0, 0);
    }

    #[test]
    fn test_mul_by_cofactor_public() {
        check_mul_by_cofactor(Mode::Public, 2, 0, 10, 10);
    }

    #[test]
    fn test_mul_by_cofactor_private() {
        check_mul_by_cofactor(Mode::Private, 2, 0, 10, 10);
    }

    /// This test shows that computing `mul_by_cofactor` using doubling is more cost-effective for our specific cofactor.
    #[test]
    fn test_mul_by_cofactor_matches() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());

            // Multiply the point by the inverse of the cofactor.
            let input = expected.div_by_cofactor();
            assert_eq!(expected, input.mul_by_cofactor());

            // Initialize the input.
            let affine = Group::<Circuit>::new(Mode::Private, input);

            Circuit::scope(&format!("Constant {}", i), || {
                let candidate =
                    affine * Scalar::constant(console::Scalar::new(<Circuit as Environment>::ScalarField::from(4u128)));
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(258, 0, 22, 22);
            });
            Circuit::reset();
        }
    }
}
