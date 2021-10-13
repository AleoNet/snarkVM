// Copyright (C) 2019-2021 Aleo Systems Inc.
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

pub mod add;
pub mod div;
pub mod double;
pub mod equal;
pub mod inv;
pub mod mul;
pub mod neg;
pub mod one;
pub mod square;
pub mod sub;
pub mod ternary;
pub mod to_bits;
pub mod zero;

use crate::{traits::*, Boolean, Environment, LinearCombination, Mode};
use snarkvm_fields::{Field as F, One as O};
use snarkvm_utilities::ToBits as TBits;

#[cfg(test)]
use snarkvm_fields::Zero as Z;

use num_traits::Inv;
use std::{
    fmt,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Clone)]
pub struct Field<E: Environment>(LinearCombination<E::BaseField>);

impl<E: Environment> Field<E> {
    ///
    /// Initializes a new instance of a field from a constant field element.
    ///
    pub fn new(mode: Mode, value: E::BaseField) -> Self {
        Self(E::new_variable(mode, value).into())
    }

    ///
    /// Initializes a new instance of a field from a boolean.
    ///
    pub fn from(boolean: &Boolean<E>) -> Self {
        Self((**boolean).clone())
    }

    ///
    /// Returns `true` if the field is a constant.
    ///
    pub fn is_constant(&self) -> bool {
        self.0.is_constant()
    }

    ///
    /// Ejects the field as a constant field element.
    ///
    pub fn eject_value(&self) -> E::BaseField {
        self.0.to_value()
    }
}

impl<E: Environment> fmt::Debug for Field<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> From<Field<E>> for LinearCombination<E::BaseField> {
    fn from(field: Field<E>) -> Self {
        field.0
    }
}

impl<E: Environment> From<&Field<E>> for LinearCombination<E::BaseField> {
    fn from(field: &Field<E>) -> Self {
        field.0.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;
    use std::str::FromStr;

    const ITERATIONS: usize = 10_000;

    /// Attempts to construct a field from the given element and mode,
    /// format it in debug mode, and recover a field from it.
    fn check_debug(mode: Mode, element: <Circuit as Environment>::BaseField) {
        let candidate = Field::<Circuit>::new(mode, element);
        assert_eq!(element.to_string(), format!("{:?}", candidate));

        let candidate_element = <Circuit as Environment>::BaseField::from_str(&format!("{:?}", candidate)).unwrap();
        let candidate_recovered = Field::<Circuit>::new(mode, candidate_element);
        assert_eq!(candidate.eject_value(), candidate_recovered.eject_value());
    }

    #[test]
    fn test_debug() {
        for _ in 0..ITERATIONS {
            let element = UniformRand::rand(&mut thread_rng());

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
        let zero = <Circuit as Environment>::BaseField::zero();

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, zero);
        assert_eq!("0", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_one() {
        let one = <Circuit as Environment>::BaseField::one();

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, one);
        assert_eq!("1", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_two() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        // Constant
        let candidate = Field::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Public
        let candidate = Field::<Circuit>::new(Mode::Public, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Private
        let candidate = Field::<Circuit>::new(Mode::Private, two);
        assert_eq!("2", &format!("{:?}", candidate));
    }
}
