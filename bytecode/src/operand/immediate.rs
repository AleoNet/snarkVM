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

use snarkvm_circuits::{
    Affine,
    Annotation,
    BaseField,
    Boolean,
    Eject,
    Environment,
    Mode,
    Parser,
    ParserResult,
    Scalar,
};

use core::fmt;
use nom::{branch::alt, combinator::map};

#[derive(Clone)]
pub enum Immediate<E: Environment> {
    Boolean(Boolean<E>),
    Field(BaseField<E>),
    Group(Affine<E>),
    Scalar(Scalar<E>),
}

impl<E: Environment> Immediate<E> {
    /// Returns the type name of the immediate.
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Boolean(..) => Boolean::<E>::type_name(),
            Self::Field(..) => BaseField::<E>::type_name(),
            Self::Group(..) => Affine::<E>::type_name(),
            Self::Scalar(..) => Scalar::<E>::type_name(),
        }
    }

    /// Returns the mode of the immediate.
    pub fn mode(&self) -> Mode {
        match self {
            Self::Boolean(boolean) => boolean.eject_mode(),
            Self::Field(field) => field.eject_mode(),
            Self::Group(group) => group.eject_mode(),
            Self::Scalar(scalar) => scalar.eject_mode(),
        }
    }

    /// Returns `true` if the immediate is a constant.
    pub fn is_constant(&self) -> bool {
        self.mode().is_constant()
    }

    /// Returns `true` if the immediate is public.
    pub fn is_public(&self) -> bool {
        self.mode().is_public()
    }

    /// Returns `true` if the immediate is private.
    pub fn is_private(&self) -> bool {
        self.mode().is_private()
    }
}

impl<E: Environment> Parser for Immediate<E> {
    type Environment = E;

    /// Parses a string into an immediate.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Boolean::parse, |boolean| Self::Boolean(boolean)),
            map(BaseField::parse, |field| Self::Field(field)),
            map(Affine::parse, |group| Self::Group(group)),
            map(Scalar::parse, |scalar| Self::Scalar(scalar)),
        ))(string)
    }
}

impl<E: Environment> fmt::Display for Immediate<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Boolean(boolean) => boolean.fmt(f),
            Self::Field(field) => field.fmt(f),
            Self::Group(group) => group.fmt(f),
            Self::Scalar(scalar) => scalar.fmt(f),
        }
    }
}
