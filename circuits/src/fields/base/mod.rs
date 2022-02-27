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

pub mod add;
pub mod div;
pub mod double;
pub mod equal;
pub mod from_bits;
pub mod inv;
pub mod mul;
pub mod neg;
pub mod one;
pub mod square;
pub mod sub;
pub mod ternary;
pub mod to_bits;
pub mod to_lower_bits;
pub mod to_upper_bits;
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
pub struct BaseField<E: Environment>(LinearCombination<E::BaseField>);

impl<E: Environment> BaseFieldTrait for BaseField<E> {}

impl<E: Environment> BaseField<E> {
    ///
    /// Initializes a new instance of a base field from a constant base field value.
    ///
    pub fn new(mode: Mode, value: E::BaseField) -> Self {
        Self(E::new_variable(mode, value).into())
    }

    ///
    /// Initializes a new instance of a base field from a boolean.
    ///
    pub fn from(boolean: &Boolean<E>) -> Self {
        Self((**boolean).clone())
    }
}

impl<E: Environment> Eject for BaseField<E> {
    type Primitive = E::BaseField;

    ///
    /// Ejects the mode of the base field.
    ///
    fn eject_mode(&self) -> Mode {
        self.0.to_mode()
    }

    ///
    /// Ejects the base field as a constant base field value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        self.0.to_value()
    }
}

// impl<E: Environment> Parser for BaseField<E> {
//     type Output = BaseField<E>;
//
//     ///
//     /// Parses a string into a circuit type.
//     ///
//     /// # Examples
//     ///
//     /// ```
//     /// use snarkvm_circuits::{Parser, Circuit, Eject, Boolean};
//     ///
//     /// let candidate = Boolean::<Circuit>::parse("true");
//     /// assert_eq!(true, candidate.eject_value());
//     /// assert!(candidate.is_constant());
//     ///
//     /// let candidate = Boolean::<Circuit>::parse("false");
//     /// assert_eq!(false, candidate.eject_value());
//     /// assert!(candidate.is_constant());
//     /// ```
//     #[inline]
//     fn parse(boolean: &str) -> Self::Output {
//         match boolean {
//             "true" => Boolean::new(Mode::Constant, true),
//             "false" => Boolean::new(Mode::Constant, false),
//             _ => E::halt(format!("Parser failed on 'boolean' type: {}", boolean)),
//         }
//     }
// }

impl<E: Environment> fmt::Debug for BaseField<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> fmt::Display for BaseField<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({})", self.eject_mode(), self.eject_value())
    }
}

impl<E: Environment> From<BaseField<E>> for LinearCombination<E::BaseField> {
    fn from(field: BaseField<E>) -> Self {
        From::from(&field)
    }
}

impl<E: Environment> From<&BaseField<E>> for LinearCombination<E::BaseField> {
    fn from(field: &BaseField<E>) -> Self {
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
        let candidate = BaseField::<Circuit>::new(mode, element);
        assert_eq!(element.to_string(), format!("{:?}", candidate));

        let candidate_element = <Circuit as Environment>::BaseField::from_str(&format!("{:?}", candidate)).unwrap();
        let candidate_recovered = BaseField::<Circuit>::new(mode, candidate_element);
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
        let candidate = BaseField::<Circuit>::new(Mode::Constant, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Public
        let candidate = BaseField::<Circuit>::new(Mode::Public, zero);
        assert_eq!("0", &format!("{:?}", candidate));

        // Private
        let candidate = BaseField::<Circuit>::new(Mode::Private, zero);
        assert_eq!("0", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_one() {
        let one = <Circuit as Environment>::BaseField::one();

        // Constant
        let candidate = BaseField::<Circuit>::new(Mode::Constant, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Public
        let candidate = BaseField::<Circuit>::new(Mode::Public, one);
        assert_eq!("1", &format!("{:?}", candidate));

        // Private
        let candidate = BaseField::<Circuit>::new(Mode::Private, one);
        assert_eq!("1", &format!("{:?}", candidate));
    }

    #[test]
    fn test_debug_two() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        // Constant
        let candidate = BaseField::<Circuit>::new(Mode::Constant, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Public
        let candidate = BaseField::<Circuit>::new(Mode::Public, two);
        assert_eq!("2", &format!("{:?}", candidate));

        // Private
        let candidate = BaseField::<Circuit>::new(Mode::Private, two);
        assert_eq!("2", &format!("{:?}", candidate));
    }
}
