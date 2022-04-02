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

pub mod equal;
pub mod to_bits;
pub mod to_group;

#[cfg(test)]
use snarkvm_circuits_environment::assert_scope;

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types_boolean::Boolean;
use snarkvm_circuits_types_group::Group;
use snarkvm_circuits_types_scalar::Scalar;
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use bech32::{FromBase32, ToBase32};

#[derive(Clone)]
pub struct Address<E: Environment>(Group<E>);

impl<E: Environment> AddressTrait for Address<E> {}

impl<E: Environment> Address<E> {
    ///
    /// Initializes a new instance of an address from an affine group.
    ///
    pub fn from(value: Group<E>) -> Self {
        Self(value)
    }
}

impl<E: Environment> Inject for Address<E> {
    type Primitive = E::Affine;

    ///
    /// Initializes a new instance of an address from a string.
    ///
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        Self(Group::new(mode, value))
    }
}

impl<E: Environment> Eject for Address<E> {
    type Primitive = E::Affine;

    ///
    /// Ejects the mode of the group element.
    ///
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    ///
    /// Ejects the address as a constant affine group element.
    ///
    fn eject_value(&self) -> Self::Primitive {
        self.0.eject_value()
    }
}

impl<E: Environment> Parser for Address<E> {
    type Environment = E;

    /// Parses a string into an address circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the 'aleo1' keyword from the string.
        let (string, _) = tag("aleo1")(string)?;
        // Parse the digits from the string.
        let (string, primitive) =
            recognize(many1(terminated(one_of("qpzry9x8gf2tvdw0s3jn54khce6mua7l"), many0(char('_')))))(string)?;
        // Parse the value from the string.
        let (string, value) = map_res(tag(Self::type_name()), |_| {
            let address = primitive.replace('_', "");
            if address.len() != 63 {
                return Err(error(format!("Invalid address length of {}", address.len())));
            }

            let (hrp, data, variant) = bech32::decode(&address).map_err(|e| error(format!("{e}")))?;
            if hrp != "aleo" {
                return Err(error(format!("Invalid address prefix of {hrp}")));
            }
            if data.is_empty() {
                return Err(error("Invalid byte length of 0"));
            }
            if variant != bech32::Variant::Bech32m {
                eprintln!("[Warning] This Aleo address is in bech32 (deprecated)");
            }

            let buffer = Vec::from_base32(&data).map_err(|e| error(format!("{e}")))?;
            Ok(E::affine_from_x_coordinate(E::BaseField::read_le(&buffer[..])?))
        })(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Address::new(mode, value))),
            None => Ok((string, Address::new(Mode::Constant, value))),
        }
    }
}

impl<E: Environment> TypeName for Address<E> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        "address"
    }
}

impl<E: Environment> Debug for Address<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> Display for Address<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Convert the x-coordinate to bytes.
        let encryption_key = match self.eject_value().to_x_coordinate().to_bytes_le() {
            Ok(encryption_key) => encryption_key,
            Err(error) => E::halt(format!("Failed to convert the address into bytes: {error}")),
        };

        // Encode in bech32m.
        let address = match bech32::encode("aleo", encryption_key.to_base32(), bech32::Variant::Bech32m) {
            Ok(address) => address,
            Err(error) => E::halt(format!("Failed to encode in bech32m: {error}")),
        };

        write!(f, "{}.{}", address, self.eject_mode())
    }
}
