// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod equal;
mod from_bits;
mod from_fields;
mod num_randomizers;
mod size_in_fields;
mod to_bits;
mod to_fields;

use crate::Visibility;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field};

use core::ops::Deref;

#[derive(Clone)]
pub struct Data<A: Aleo>(Vec<Field<A>>);

#[cfg(console)]
impl<A: Aleo> Inject for Data<A> {
    type Primitive = console::Data<A::Network>;

    /// Initializes a new `Data` circuit from a primitive.
    fn new(mode: Mode, ciphertext: Self::Primitive) -> Self {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match (*ciphertext).len() <= A::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Self(Inject::new(mode, (*ciphertext).to_vec())),
            false => A::halt("Data exceeds maximum allowed size"),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Data<A> {
    type Primitive = console::Data<A::Network>;

    /// Ejects the mode of the `Data`.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the `Data`.
    fn eject_value(&self) -> Self::Primitive {
        match console::FromFields::from_fields(&self.0.eject_value()) {
            Ok(data) => data,
            Err(error) => A::halt(format!("Failed to eject data: {error}")),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Parser for Data<A> {
    /// Parses a UTF-8 string into a `Data`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the `Data` from the string.
        let (string, data) = console::Data::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Data::new(mode, data))),
            None => Ok((string, Data::new(Mode::Constant, data))),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> FromStr for Data<A> {
    type Err = Error;

    /// Parses a UTF-8 string into a `Data`.
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
impl<A: Aleo> Debug for Data<A> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl<A: Aleo> Display for Data<A> {
    /// Prints the `Data` as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<A: Aleo> Deref for Data<A> {
    type Target = [Field<A>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
