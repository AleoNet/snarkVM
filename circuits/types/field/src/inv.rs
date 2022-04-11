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
use snarkvm_circuits_environment::Count;

impl<E: Environment> Inv for Field<E> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        (&self).inv()
    }
}

impl<E: Environment> Inv for &Field<E> {
    type Output = Field<E>;

    fn inv(self) -> Self::Output {
        let inverse = witness!(|self| match self.inverse() {
            Some(inverse) => inverse,
            None => E::halt("Failed to compute the inverse for a base field element"),
        });

        // Ensure self * self^(-1) == 1.
        E::enforce(|| (self, &inverse, E::one()));

        inverse
    }
}

impl<E: Environment> MetadataForOp<dyn Inv<Output = Field<E>>> for Field<E> {
    type Case = Mode;

    fn count(input: &Self::Case) -> Count {
        match input.is_constant() {
            true => Count::exact(1, 0, 0, 0),
            false => Count::exact(0, 0, 1, 1),
        }
    }

    fn output_mode(input: &Self::Case) -> Mode {
        match input {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 1_000;

    fn check_inv(
        name: &str,
        mode: Mode,
    ) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            // Compute it's inverse, or skip this iteration if it does not natively exist.
            if let Some(expected) = given.inverse() {
                let candidate = Field::<Circuit>::new(mode, given);

                Circuit::scope(name, || {
                    let result = candidate.inv();
                    assert_eq!(expected, result.eject_value());

                    // TODO: Refactor into a cleaner macro invocation.
                    let count = <Field<Circuit> as MetadataForOp::<dyn Inv<Output = Field<Circuit>>>>::count(&mode);
                    assert!(count.is_satisfied(Circuit::num_constants_in_scope(), Circuit::num_public_in_scope(), Circuit::num_private_in_scope(), Circuit::num_constraints_in_scope()));

                    let output_mode = <Field<Circuit> as MetadataForOp::<dyn Inv<Output = Field<Circuit>>>>::output_mode(&mode);
                    assert_eq!(output_mode, result.eject_mode());

                    assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
                });
                Circuit::reset();
            }
        }
    }

    #[test]
    fn test_inv() {
        check_inv("Constant", Mode::Constant);
        check_inv("Public", Mode::Public);
        check_inv("Private", Mode::Private);
    }

    #[test]
    fn test_zero_inv_fails() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let result = std::panic::catch_unwind(|| Field::<Circuit>::zero().inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Constant, zero).inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Public, zero).inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Private, zero).inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired
    }
}
