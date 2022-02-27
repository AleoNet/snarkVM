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

// pub mod add;
// pub mod div;
// pub mod double;
// pub mod inv;
// pub mod mul;
// pub mod neg;
// pub mod square;
// pub mod sub;

pub mod equal;
pub mod one;
pub mod ternary;
pub mod to_bits;
pub mod zero;

use crate::{traits::*, Boolean, Environment, Mode};
use snarkvm_fields::{One as O, PrimeField, Zero as Z};
use snarkvm_utilities::{FromBits as FBits, ToBits as TBits};

use std::fmt;

#[derive(Clone)]
pub struct ScalarField<E: Environment>(Vec<Boolean<E>>);

impl<E: Environment> ScalarField<E> {
    ///
    /// Initializes a new instance of a scalar field from a constant scalar field value.
    ///
    pub fn new(mode: Mode, value: E::ScalarField) -> Self {
        let bits = value.to_bits_le().iter().map(|bit| Boolean::new(mode, *bit)).collect::<Vec<_>>();

        Self(bits)
    }
}

impl<E: Environment> Eject for ScalarField<E> {
    type Primitive = E::ScalarField;

    ///
    /// Ejects the mode of the scalar field.
    ///
    fn eject_mode(&self) -> Mode {
        let mut scalar_mode = Mode::Constant;
        for bit_mode in self.0.iter().map(Eject::eject_mode) {
            // Check if the mode in the current iteration matches the scalar mode.
            if scalar_mode != bit_mode {
                // If they do not match, the scalar mode must be a constant.
                // Otherwise, this is a malformed scalar, and the program should halt.
                match scalar_mode == Mode::Constant {
                    true => scalar_mode = bit_mode,
                    false => E::halt("Detected an scalar field with a malformed mode"),
                }
            }
        }
        scalar_mode
    }

    ///
    /// Ejects the scalar field as a constant scalar field value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        let bits = self.0.iter().map(Boolean::eject_value).collect::<Vec<_>>();
        let biginteger = <E::ScalarField as PrimeField>::BigInteger::from_bits_le(&bits[..]);
        let scalar = <E::ScalarField as PrimeField>::from_repr(biginteger);
        match scalar {
            Some(scalar) => scalar,
            None => E::halt("Failed to eject scalar field value"),
        }
    }
}

impl<E: Environment> fmt::Debug for ScalarField<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;
    use std::str::FromStr;

    const ITERATIONS: usize = 250;

    fn check_new(
        name: &str,
        expected: <Circuit as Environment>::ScalarField,
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = ScalarField::<Circuit>::new(mode, expected);
            assert_eq!(expected, candidate.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    /// Attempts to construct a field from the given element and mode,
    /// format it in debug mode, and recover a field from it.
    fn check_debug(mode: Mode, element: <Circuit as Environment>::ScalarField) {
        let candidate = ScalarField::<Circuit>::new(mode, element);
        assert_eq!(element.to_string(), format!("{:?}", candidate));

        let candidate_element = <Circuit as Environment>::ScalarField::from_str(&format!("{:?}", candidate)).unwrap();
        let candidate_recovered = ScalarField::<Circuit>::new(mode, candidate_element);
        assert_eq!(candidate.eject_value(), candidate_recovered.eject_value());
    }

    #[test]
    fn test_new_constant() {
        let expected = UniformRand::rand(&mut thread_rng());
        check_new("Constant", expected, Mode::Constant, 251, 0, 0, 0);
    }

    #[test]
    fn test_new_public() {
        let expected = UniformRand::rand(&mut thread_rng());
        check_new("Public", expected, Mode::Public, 0, 251, 0, 251);
    }

    #[test]
    fn test_new_private() {
        let expected = UniformRand::rand(&mut thread_rng());
        check_new("Private", expected, Mode::Private, 0, 0, 251, 251);
    }

    #[test]
    fn test_debug() {
        for _ in 0..ITERATIONS {
            let element: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());

            // Constant
            check_debug(Mode::Constant, element);
            // Public
            check_debug(Mode::Public, element);
            // Private
            check_debug(Mode::Private, element);
        }
    }

    #[test]
    fn test_debug_zero() {
        let zero = <Circuit as Environment>::ScalarField::zero();

        // Constant
        let candidate = ScalarField::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Public
        let candidate = ScalarField::<Circuit>::new(Mode::Public, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Private
        let candidate = ScalarField::<Circuit>::new(Mode::Private, zero);
        assert_eq!("0", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_one() {
        let one = <Circuit as Environment>::ScalarField::one();

        // Constant
        let candidate = ScalarField::<Circuit>::new(Mode::Constant, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Public
        let candidate = ScalarField::<Circuit>::new(Mode::Public, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Private
        let candidate = ScalarField::<Circuit>::new(Mode::Private, one);
        assert_eq!("1", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_two() {
        let one = <Circuit as Environment>::ScalarField::one();
        let two = one + one;

        // Constant
        let candidate = ScalarField::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Public
        let candidate = ScalarField::<Circuit>::new(Mode::Public, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Private
        let candidate = ScalarField::<Circuit>::new(Mode::Private, two);
        assert_eq!("2", &format!("{:?}", candidate));
    }
}
