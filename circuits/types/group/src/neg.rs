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

impl<E: Environment> Neg for Group<E> {
    type Output = Self;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        Group { x: -self.x, y: self.y }
    }
}

impl<E: Environment> Neg for &Group<E> {
    type Output = Group<E>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

impl<E: Environment> Metadata<dyn Neg<Output = Group<E>>> for Group<E> {
    type Case = CircuitType<Self>;
    type OutputType = CircuitType<Self>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(constant) => CircuitType::from(constant.circuit().neg()),
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_neg(name: &str, expected: <Circuit as Environment>::Affine, candidate_input: Group<Circuit>) {
        Circuit::scope(name, || {
            let candidate_output = -&(candidate_input);
            assert_eq!(expected, candidate_output.eject_value());

            let case = CircuitType::from(candidate_input);
            assert_count!(Neg(Group) => Group, &case);
            assert_output_type!(Neg(Group) => Group, case, candidate_output);
        });
    }

    fn run_test(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let expected = -point;
            assert!(expected.is_on_curve());
            assert!(expected.is_in_correct_subgroup_assuming_on_curve());

            let candidate_input = Group::<Circuit>::new(mode, point);
            check_neg(&format!("NEG {} {}", mode, i), expected, candidate_input);
        }

        // Test zero case.
        let expected = <Circuit as Environment>::Affine::zero();
        let candidate_input = Group::<Circuit>::zero();
        check_neg(&format!("NEG {} Zero", mode), expected, candidate_input);
    }

    #[test]
    fn test_neg_constant() {
        run_test(Mode::Constant)
    }

    #[test]
    fn test_neg_public() {
        run_test(Mode::Public);
    }

    #[test]
    fn test_neg_private() {
        run_test(Mode::Private)
    }
}
