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

#![forbid(unsafe_code)]

mod helpers;

mod compare;
mod equal;
mod ternary;

#[cfg(test)]
use console::{test_rng, Uniform};
#[cfg(test)]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuit_environment::prelude::*;
use snarkvm_circuit_types_boolean::Boolean;
use snarkvm_circuit_types_field::Field;
use snarkvm_circuit_types_group::Group;
use snarkvm_circuit_types_scalar::Scalar;

use core::str::FromStr;

#[derive(Clone)]
pub struct Address<E: Environment>(Group<E>);

impl<E: Environment> AddressTrait for Address<E> {}

#[cfg(console)]
impl<E: Environment> Inject for Address<E> {
    type Primitive = console::Address<E::Network>;

    /// Initializes a new instance of an address.
    fn new(mode: Mode, address: Self::Primitive) -> Self {
        Self(Group::new(mode, *address))
    }
}

#[cfg(console)]
impl<E: Environment> Eject for Address<E> {
    type Primitive = console::Address<E::Network>;

    /// Ejects the mode of the address.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the address.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::new(self.0.eject_value())
    }
}

#[cfg(console)]
impl<E: Environment> Parser for Address<E> {
    /// Parses a string into an address circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the address from the string.
        let (string, address) = console::Address::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Address::new(mode, address))),
            None => Ok((string, Address::new(Mode::Constant, address))),
        }
    }
}

#[cfg(console)]
impl<E: Environment> FromStr for Address<E> {
    type Err = Error;

    /// Parses a string into a address.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

#[cfg(console)]
impl<E: Environment> TypeName for Address<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        console::Address::<E::Network>::type_name()
    }
}

#[cfg(console)]
impl<E: Environment> Debug for Address<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl<E: Environment> Display for Address<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}

impl<E: Environment> From<Address<E>> for LinearCombination<E::BaseField> {
    fn from(address: Address<E>) -> Self {
        From::from(&address)
    }
}

impl<E: Environment> From<&Address<E>> for LinearCombination<E::BaseField> {
    fn from(address: &Address<E>) -> Self {
        From::from(address.to_field())
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    #[test]
    fn test_address_parse() {
        let expected = "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public";
        let address = Address::<Circuit>::parse(expected).unwrap().1;
        assert_eq!(expected, &format!("{address}"));
    }
}
