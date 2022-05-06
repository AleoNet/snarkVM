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

impl<E: Environment> Neg for Field<E> {
    type Output = Self;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

impl<E: Environment> Neg for &Field<E> {
    type Output = Field<E>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (-&self.linear_combination).into()
    }
}

impl<E: Environment> Metadata<dyn Neg<Output = Field<E>>> for Field<E> {
    type Case = CircuitType<Field<E>>;
    type OutputType = CircuitType<Field<E>>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case.is_constant() {
            true => CircuitType::from(case.circuit().neg()),
            false => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 1_000;

    fn check_neg(name: &str, mode: Mode) {
        let check_neg = |given: <Circuit as Environment>::BaseField| {
            // Compute it's negation.
            let expected = given.neg();
            let candidate = Field::<Circuit>::new(mode, given);

            // Check negation.
            Circuit::scope(name, || {
                let result = (&candidate).neg();
                assert_eq!(expected, result.eject_value());

                let case = CircuitType::from(candidate);
                assert_count!(Neg(Field) => Field, &case);
                assert_output_type!(Neg(Field) => Field, case, result);
            });
        };

        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            check_neg(given)
        }
        // Check zero case.
        check_neg(<Circuit as Environment>::BaseField::zero());
        // Check one case.
        check_neg(<Circuit as Environment>::BaseField::one());
    }

    #[test]
    fn test_neg() {
        check_neg("Constant", Mode::Constant);
        check_neg("Public", Mode::Public);
        check_neg("Private", Mode::Private);
    }

    #[test]
    fn test_zero() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = Field::<Circuit>::zero();
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Public, zero);
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());
    }

    #[test]
    fn test_one() {
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = Field::<Circuit>::one();
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one);
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one);
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());
    }
}
