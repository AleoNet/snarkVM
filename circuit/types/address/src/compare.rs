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

impl<E: Environment> Compare<Address<E>> for Address<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Self) -> Self::Output {
        self.0.to_x_coordinate().is_less_than(&other.0.to_x_coordinate())
    }

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Self) -> Self::Output {
        other.is_less_than(self)
    }

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Self) -> Self::Output {
        other.is_greater_than_or_equal(self)
    }

    /// Returns `true` if `self` is greater than or equal to `other`.
    fn is_greater_than_or_equal(&self, other: &Self) -> Self::Output {
        !self.is_less_than(other)
    }
}

// TODO: Implement `Metrics` and `OutputMode` for `Compare`. Waiting for PR#711  to land as it significantly changes the counts.

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    #[allow(clippy::too_many_arguments)]
    fn check_is_less_than(
        name: &str,
        expected: bool,
        a: &Address<Circuit>,
        b: &Address<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        // Perform the less than comparison.
        Circuit::scope(name, || {
            let candidate = a.is_less_than(b);
            assert_eq!(expected, candidate.eject_value());
            match (a.eject_mode(), b.eject_mode()) {
                (Mode::Constant, Mode::Constant) => {
                    assert_scope!(num_constants, num_public, num_private, num_constraints)
                }
                (_, Mode::Constant) | (Mode::Constant, _) => {
                    assert_scope!(<=num_constants, <=num_public, <=num_private, <=num_constraints)
                }
                _ => assert_scope!(num_constants, num_public, num_private, num_constraints),
            }
        });
        Circuit::reset();
    }

    fn run_test(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let a = Address::<Circuit>::new(mode_a, console::Address::new(first));
            let b = Address::<Circuit>::new(mode_b, console::Address::new(second));
            let expected = first.to_x_coordinate() < second.to_x_coordinate();
            let name = format!("{} {} {}", mode_a, mode_b, i);
            check_is_less_than(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);

            // Check `first` is not less than `first`.
            let a = Address::<Circuit>::new(mode_a, console::Address::new(first));
            let b = Address::<Circuit>::new(mode_b, console::Address::new(first));
            check_is_less_than(
                "first !< first",
                false,
                &a,
                &b,
                num_constants,
                num_public,
                num_private,
                num_constraints,
            );
        }
    }

    #[test]
    fn test_constant_is_less_than_constant() {
        run_test(Mode::Constant, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_is_less_than_public() {
        run_test(Mode::Constant, Mode::Public, 253, 0, 506, 507);
    }

    #[test]
    fn test_constant_is_less_than_private() {
        run_test(Mode::Constant, Mode::Private, 253, 0, 506, 507);
    }

    #[test]
    fn test_public_is_less_than_constant() {
        run_test(Mode::Public, Mode::Constant, 253, 0, 506, 507);
    }

    #[test]
    fn test_public_is_less_than_public() {
        run_test(Mode::Public, Mode::Public, 0, 0, 1012, 1014);
    }

    #[test]
    fn test_public_is_less_than_private() {
        run_test(Mode::Public, Mode::Private, 0, 0, 1012, 1014);
    }

    #[test]
    fn test_private_is_less_than_constant() {
        run_test(Mode::Private, Mode::Constant, 253, 0, 506, 507);
    }

    #[test]
    fn test_private_is_less_than_public() {
        run_test(Mode::Private, Mode::Public, 0, 0, 1012, 1014);
    }

    #[test]
    fn test_private_is_less_than_private() {
        run_test(Mode::Private, Mode::Private, 0, 0, 1012, 1014);
    }
}
