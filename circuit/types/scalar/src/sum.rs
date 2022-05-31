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

impl<E: Environment> Sum<Scalar<E>> for Scalar<E> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Scalar::zero(), |a, b| &a + &b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 128;
    const NUM_ELEMENTS: usize = 16;

    #[rustfmt::skip]
    fn check_sum(
        name: &str,
        elements: &[<Circuit as Environment>::ScalarField],
        modes: &[Mode],
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let mut result = Vec::new();

        for (element, mode) in elements.iter().zip_eq(modes) {
            result.push(Scalar::<Circuit>::new(*mode, *element));
        }

        let expected: <Circuit as Environment>::ScalarField = elements.iter().sum();

        Circuit::scope(name, || {
            let candidate: Scalar<Circuit> = result.into_iter().sum();
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(<=num_constants, <=num_public, <=num_private, <=num_constraints);
        });
    }

    #[rustfmt::skip]
    fn run_test(
        options: &[Mode],
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let modes: Vec<Mode> = (0..NUM_ELEMENTS).map(|i| options[i % options.len()]).collect();

        for i in 0..ITERATIONS {
            let elements: Vec<_> = (0..modes.len()).map(|_| UniformRand::rand(&mut test_rng())).collect();

            let name = format!("Sum: {:?} {i}", options);
            check_sum(&name, &elements, &modes, num_constants, num_public, num_private, num_constraints);
        }
    }

    #[test]
    fn test_scalar_sum_constant() {
        let options = [Mode::Constant];

        run_test(&options, 4267, 0, 0, 0);
    }

    #[test]
    fn test_scalar_sum_public() {
        let options = [Mode::Public];

        run_test(&options, 4315, 0, 12112, 12144);
    }

    #[test]
    fn test_scalar_sum_private() {
        let options = [Mode::Private];

        run_test(&options, 4315, 0, 12112, 12144);
    }

    #[test]
    fn test_scalar_sum_constant_and_public() {
        let options = [Mode::Constant, Mode::Public];

        run_test(&options, 4315, 0, 12112, 12144);
    }

    #[test]
    fn test_scalar_sum_constant_and_private() {
        let options = [Mode::Constant, Mode::Private];

        run_test(&options, 4315, 0, 12112, 12144);
    }

    #[test]
    fn test_scalar_sum_public_and_private() {
        let options = [Mode::Public, Mode::Private];

        run_test(&options, 4315, 0, 12112, 12144);
    }

    #[test]
    fn test_scalar_sum_constant_public_and_private() {
        let options = [Mode::Constant, Mode::Public, Mode::Private];

        run_test(&options, 4315, 0, 12112, 12144);
    }
}
