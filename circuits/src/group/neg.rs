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

impl<E: Environment> Neg for Affine<E> {
    type Output = Self;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        Affine { x: -self.x, y: self.y }
    }
}

impl<E: Environment> Neg for &Affine<E> {
    type Output = Affine<E>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_neg(
        name: &str,
        expected: <Circuit as Environment>::Affine,
        candidate_input: Affine<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate_output = -candidate_input;
            assert_eq!(expected, candidate_output.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_neg_constant() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input =
                Affine::<Circuit>::new(Mode::Constant, point.to_x_coordinate(), Some(point.to_y_coordinate()));
            check_neg(&format!("NEG Constant {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_public() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input =
                Affine::<Circuit>::new(Mode::Public, point.to_x_coordinate(), Some(point.to_y_coordinate()));
            check_neg(&format!("NEG Public {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_neg_private() {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut thread_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input =
                Affine::<Circuit>::new(Mode::Private, point.to_x_coordinate(), Some(point.to_y_coordinate()));
            check_neg(&format!("NEG Private {}", i), expected, candidate_input, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_zero() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let expected = <Circuit as Environment>::Affine::zero();

        let candidate_input = Affine::<Circuit>::zero();
        check_neg("NEG Constant Zero", expected, candidate_input, 0, 0, 0, 0);

        let candidate_input = Affine::<Circuit>::new(Mode::Public, zero, None);
        check_neg("NEG Public Zero", expected, candidate_input, 0, 0, 0, 0);

        let candidate_input = Affine::<Circuit>::new(Mode::Private, zero, None);
        check_neg("NEG Private Zero", expected, candidate_input, 0, 0, 0, 0);
    }
}
