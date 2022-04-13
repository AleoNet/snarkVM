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

pub mod address;
pub use address::*;

pub mod boolean;
pub use boolean::*;

pub mod eject;
pub use eject::*;

pub mod field;
pub use field::*;

pub mod from;
pub use from::*;

pub mod group;
pub use group::*;

pub mod inject;
pub use inject::*;

pub mod integers;
pub use integers::{
    integer_type::{CheckedPow, IntegerProperties, IntegerType, WrappingDiv, WrappingPow, WrappingRem},
    magnitude::Magnitude,
    IntegerCore,
    IntegerTrait,
};

pub mod metadata;
pub use metadata::*;

pub mod operators;
pub use operators::*;

pub mod scalar;
pub use scalar::*;

pub mod string;
pub use string::*;

pub mod to;
pub use to::*;

pub mod to_bits;
pub use to_bits::*;

use crate::Environment;

use core::fmt::Display;
use nom::{error::VerboseError, IResult};

pub type ParserResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

/// Operations to parse a string literal into an object.
pub trait Parser: Display {
    type Environment: Environment;

    ///
    /// Parses a string literal into an object.
    ///
    fn parse(s: &str) -> ParserResult<Self>
    where
        Self: Sized;

    ///
    /// Returns an object from a string literal.
    ///
    fn from_str(string: &str) -> Self
    where
        Self: Sized,
    {
        match Self::parse(string) {
            Ok((remainder, circuit)) => match remainder.is_empty() {
                true => circuit,
                false => Self::Environment::halt(format!(
                    "Failed to parse string. Found invalid character in: \"{remainder}\""
                )),
            },
            Err(error) => Self::Environment::halt(format!("Failed to parse string. {error}")),
        }
    }
}

pub trait TypeName {
    ///
    /// Returns the type name of the object as a string. (i.e. "u8")
    ///
    fn type_name() -> &'static str;
}
