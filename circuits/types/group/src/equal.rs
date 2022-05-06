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

// TODO: Split into multiple traits.

impl<E: Environment> Equal<Self> for Group<E> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// This method costs 8 constraints.
    ///
    fn is_equal(&self, other: &Self) -> Self::Output {
        let is_x_eq = self.x.is_equal(&other.x);
        let is_y_eq = self.y.is_equal(&other.y);
        is_x_eq & is_y_eq
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    /// This method costs 8 constraints.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

impl<E: Environment> Metadata<dyn Equal<Group<E>, Output = Boolean<E>>> for Group<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(2, 0, 0, 0),
            _ => Count::is(0, 0, 5, 7),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => {
                CircuitType::from(case.0.circuit().is_equal(case.1.circuit()))
            }
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

    #[test]
    fn test_is_equal() {
        // Constant == Constant
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            let a = Group::<Circuit>::new(Mode::Constant, a);
            let b = Group::<Circuit>::new(Mode::Constant, b);

            Circuit::scope(&format!("Constant Equals {}", i), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(2, 0, 0, 0);
            });
            Circuit::reset();

            Circuit::scope(&format!("Constant Not Equals {}", i), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(2, 0, 0, 0);
            });
            Circuit::reset();
        }

        // Constant == Public
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            let a = Group::<Circuit>::new(Mode::Constant, a);
            let b = Group::<Circuit>::new(Mode::Public, b);

            Circuit::scope(&format!("Constant and Public Equals {}", i), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();

            Circuit::scope(&format!("Constant and Public Not Equals {}", i), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();
        }

        // Public == Constant
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            let a = Group::<Circuit>::new(Mode::Public, a);
            let b = Group::<Circuit>::new(Mode::Constant, b);

            Circuit::scope(&format!("Public and Constant Equals {}", i), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();

            Circuit::scope(&format!("Public and Constant Not Equals {}", i), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();
        }

        // Public == Public
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            let a = Group::<Circuit>::new(Mode::Public, a);
            let b = Group::<Circuit>::new(Mode::Public, b);

            Circuit::scope(&format!("Public Equals {}", i), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();

            Circuit::scope(&format!("Public Not Equals {}", i), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();
        }

        // Private == Private
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());

            let a = Group::<Circuit>::new(Mode::Private, a);
            let b = Group::<Circuit>::new(Mode::Private, b);

            Circuit::scope(&format!("Private Equals {}", i), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();

            Circuit::scope(&format!("Private Not Equals {}", i), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(0, 0, 5, 7);
            });
            Circuit::reset();
        }
    }
}
