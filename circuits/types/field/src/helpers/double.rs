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

impl<E: Environment> Double for Field<E> {
    type Output = Field<E>;

    fn double(self) -> Self::Output {
        (&self).double()
    }
}

impl<E: Environment> Double for &Field<E> {
    type Output = Field<E>;

    fn double(self) -> Self::Output {
        self + self
    }
}

impl<E: Environment> Metadata<dyn Double<Output = Field<E>>> for Field<E> {
    type Case = CircuitType<Field<E>>;
    type OutputType = CircuitType<Field<E>>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case.is_constant() {
            true => CircuitType::from(case.circuit().double()),
            false => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 10_000;

    fn check_double(name: &str, mode: Mode) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate = Field::<Circuit>::new(mode, given);

            Circuit::scope(name, || {
                let result = (&candidate).double();
                assert_eq!(given.double(), result.eject_value());

                let case = CircuitType::from(candidate);
                assert_count!(Double(Field) => Field, &case);
                assert_output_type!(Double(Field) => Field, case, result);
            });
        }
    }

    #[test]
    fn test_double() {
        check_double("Constant", Mode::Constant);
        check_double("Public", Mode::Public);
        check_double("Private", Mode::Private);
    }

    #[test]
    fn test_0_double() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = Field::<Circuit>::new(Mode::Public, zero).double();
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_1_double() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        let candidate = Field::<Circuit>::new(Mode::Public, one).double();
        assert_eq!(two, candidate.eject_value());
    }
}
