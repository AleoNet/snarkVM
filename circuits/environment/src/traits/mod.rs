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

pub mod field;
pub use field::*;

pub mod group;
pub use group::*;

pub mod integers;
pub use integers::{
    integer_type::{CheckedPow, IntegerProperties, IntegerType, WrappingDiv, WrappingPow, WrappingRem},
    magnitude::Magnitude,
    IntegerCore,
    IntegerTrait,
};

pub mod operators;
pub use operators::*;

pub mod scalar;
pub use scalar::*;

pub mod string;
pub use string::*;

use crate::{Environment, Mode};

use core::fmt::{Debug, Display};
use nom::{error::VerboseError, IResult};

/// Operations to convert to and from bit representation in a circuit environment.
pub trait DataType<B: BooleanTrait>: FromBits<Boolean = B> + ToBits<Boolean = B> {}

/// Operations to inject from a primitive form into a circuit environment.
pub trait Inject {
    type Primitive: Debug + Default;

    ///
    /// Returns the type name of the object as a string. (i.e. "u8")
    ///
    fn type_name() -> &'static str;

    ///
    /// Initializes a circuit of the given mode and primitive value.
    ///
    fn new(mode: Mode, value: Self::Primitive) -> Self;

    ///
    /// Initializes a constant circuit of the given primitive value.
    ///
    fn constant(value: Self::Primitive) -> Self
    where
        Self: Sized,
    {
        Self::new(Mode::Constant, value)
    }

    ///
    /// Initializes a blank default of the circuit for the given mode.
    /// This operation is used commonly to derive a proving and verifying key.
    ///
    fn blank(mode: Mode) -> Self
    where
        Self: Sized,
    {
        Self::new(mode, Default::default())
    }
}

/// Operations to eject from a circuit environment into primitive form.
pub trait Eject {
    type Primitive: Debug + Display;

    ///
    /// Ejects the mode and primitive value of the circuit type.
    ///
    fn eject(&self) -> (Mode, Self::Primitive) {
        (self.eject_mode(), self.eject_value())
    }

    ///
    /// Ejects the mode of the circuit type.
    ///
    fn eject_mode(&self) -> Mode;

    ///
    /// Ejects the circuit type as a primitive value.
    ///
    fn eject_value(&self) -> Self::Primitive;

    ///
    /// Returns `true` if the circuit is a constant.
    ///
    fn is_constant(&self) -> bool {
        self.eject_mode().is_constant()
    }

    ///
    /// Returns `true` if the circuit is a public.
    ///
    fn is_public(&self) -> bool {
        self.eject_mode().is_public()
    }

    ///
    /// Returns `true` if the circuit is a private.
    ///
    fn is_private(&self) -> bool {
        self.eject_mode().is_private()
    }
}

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
            Ok((_, circuit)) => circuit,
            Err(error) => Self::Environment::halt(format!("Failed to parse: {}", error)),
        }
    }
}

/// Representation of the zero value.
pub trait Zero {
    type Boolean: BooleanTrait;

    /// Returns a new zero constant.
    fn zero() -> Self;

    /// Returns `true` if `self` is zero.
    fn is_zero(&self) -> Self::Boolean;
}

/// Representation of the one value.
pub trait One {
    type Boolean: BooleanTrait;

    /// Returns a new one constant.
    fn one() -> Self;

    /// Returns `true` if `self` is one.
    fn is_one(&self) -> Self::Boolean;
}

/// Unary operator for retrieving the most-significant bit.
pub trait MSB {
    type Boolean: BooleanTrait;

    /// Returns the MSB of the value.
    fn msb(&self) -> &Self::Boolean;
}

/// Unary operator for instantiating from bits.
pub trait FromBits {
    type Boolean: BooleanTrait;

    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self
    where
        Self: Sized;

    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self
    where
        Self: Sized;
}

/// Unary operator for converting to bits.
pub trait ToBits {
    type Boolean: BooleanTrait;

    fn to_bits_le(&self) -> Vec<Self::Boolean>;

    fn to_bits_be(&self) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to `k` number of bits.
pub trait ToLowerBits {
    type Boolean: BooleanTrait;

    ///
    /// Outputs the lower `k` bits of an `n`-bit element in little-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_le(&self, k: usize) -> Vec<Self::Boolean>;

    ///
    /// Outputs the lower `k` bits of an `n`-bit element in big-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_be(&self, k: usize) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to `k` number of bits.
pub trait ToUpperBits {
    type Boolean: BooleanTrait;

    ///
    /// Outputs the upper `k` bits of an `n`-bit element in little-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_le(&self, k: usize) -> Vec<Self::Boolean>;

    ///
    /// Outputs the upper `k` bits of an `n`-bit element in big-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_be(&self, k: usize) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to a base field.
pub trait ToField {
    type Boolean: BooleanTrait;
    type Field: FieldTrait<Self::Boolean>;

    /// Casts a circuit into a base field.
    fn to_field(&self) -> Self::Field;
}

/// Unary operator for converting to a list of base fields.
pub trait ToFields {
    type Boolean: BooleanTrait;
    type Field: FieldTrait<Self::Boolean>;

    /// Casts a circuit into a list of base fields.
    fn to_fields(&self) -> Vec<Self::Field>;
}
