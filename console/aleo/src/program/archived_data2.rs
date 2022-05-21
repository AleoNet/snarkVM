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

use crate::{Address, Network, ViewKey};
use snarkvm_circuits_environment::Mode;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBits, ToBits};

use anyhow::{bail, Result};
use itertools::Itertools;

struct Literal<N: Network>(N::Field);
struct LiteralType<N: Network>(N::Field);

/// A value stored in program data.
enum Data<N: Network> {
    /// A constant value.
    Constant(Constant<N>),
    /// A publicly-visible value.
    Public(Public<N>),
    /// A private value encrypted under the account owner's address.
    Private(Private<N>),
}

impl<N: Network> Data<N> {
    /// Returns the recursive depth of this value.
    /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
    fn depth(&self) -> usize {
        match self {
            Self::Constant(constant) => constant.depth(0),
            Self::Public(public) => public.depth(0),
            Self::Private(private) => private.depth(0),
        }
    }

    /// Returns the identifiers that compose this value.
    fn to_identifiers(&self) -> Vec<String> {
        match self {
            Self::Constant(constant) => constant.to_identifiers(),
            Self::Public(public) => public.to_identifiers(),
            Self::Private(private) => private.to_identifiers(),
        }
    }

    /// If this value is private, returns the field elements that compose the value.
    /// Otherwise, returns `None`.
    fn to_fields(&self) -> Option<Vec<N::Field>> {
        match self {
            Self::Constant(..) => None,
            Self::Public(..) => None,
            Self::Private(private) => Some(private.to_fields()),
        }
    }

    /// Returns the mode of the value.
    pub const fn mode(&self) -> Mode {
        match self {
            Self::Constant(..) => Mode::Constant,
            Self::Public(..) => Mode::Public,
            Self::Private(..) => Mode::Private,
        }
    }

    /// Returns `true` if the value is a literal.
    pub const fn is_literal(&self) -> bool {
        matches!(
            self,
            Self::Constant(Constant::Literal(..))
                | Self::Public(Public::Literal(..))
                | Self::Private(Private::Literal(..))
        )
    }

    /// Returns `true` if the value is a composite.
    pub const fn is_composite(&self) -> bool {
        matches!(
            self,
            Self::Constant(Constant::Composite(..))
                | Self::Public(Public::Composite(..))
                | Self::Private(Private::Composite(..))
        )
    }

    /// Returns `true` if the value is constant.
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(..))
    }

    /// Returns `true` if the value is public.
    pub const fn is_public(&self) -> bool {
        matches!(self, Self::Public(..))
    }

    /// Returns `true` if the value is private.
    pub const fn is_private(&self) -> bool {
        matches!(self, Self::Private(..))
    }
}

enum Constant<N: Network> {
    /// A constant literal.
    Literal(Literal<N>),
    /// A constant composite.
    Composite(Vec<(String, Constant<N>)>),
}

impl<N: Network> Constant<N> {
    /// Returns the recursive depth of this constant value.
    /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
    fn depth(&self, counter: usize) -> usize {
        match self {
            Self::Literal(..) => 1,
            Self::Composite(composite) => {
                // Determine the maximum depth of the composite.
                let max_depth = composite.iter().map(|(_, constant)| constant.depth(counter)).fold(0, |a, b| a.max(b));
                // Add `1` to the depth of the member with the largest depth.
                max_depth.saturating_add(1)
            }
        }
    }

    /// Returns the identifiers that compose this constant value.
    fn to_identifiers(&self) -> Vec<String> {
        match self {
            Self::Literal(..) => vec![],
            Self::Composite(composite) => composite.iter().flat_map(|(identifier, constant)| {
                // Recursively get the identifiers of the member.
                let mut identifiers = vec![identifier.clone()];
                identifiers.extend(constant.to_identifiers());
                identifiers
            }).collect(),
        }
    }
}

enum Public<N: Network> {
    /// A public literal.
    Literal(Literal<N>),
    /// A public composite.
    Composite(Vec<(String, Public<N>)>),
}

impl<N: Network> Public<N> {
    /// Returns the recursive depth of this public value.
    /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
    fn depth(&self, counter: usize) -> usize {
        match self {
            Self::Literal(..) => 1,
            Self::Composite(composite) => {
                // Determine the maximum depth of the composite.
                let max_depth = composite.iter().map(|(_, public)| public.depth(counter)).fold(0, |a, b| a.max(b));
                // Add `1` to the depth of the member with the largest depth.
                max_depth.saturating_add(1)
            }
        }
    }

    /// Returns the identifiers that compose this public value.
    fn to_identifiers(&self) -> Vec<String> {
        match self {
            Self::Literal(..) => vec![],
            Self::Composite(composite) => composite.iter().flat_map(|(identifier, public)| {
                // Recursively get the identifiers of the member.
                let mut identifiers = vec![identifier.clone()];
                identifiers.extend(public.to_identifiers());
                identifiers
            }).collect(),
        }
    }
}

enum Private<N: Network> {
    /// A private literal.
    Literal(LiteralType<N>, Vec<N::Field>),
    /// A private composite.
    Composite(Vec<(String, Private<N>)>),
}

impl<N: Network> Private<N> {
    /// Returns the recursive depth of this private value.
    /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
    fn depth(&self, counter: usize) -> usize {
        match self {
            Self::Literal(..) => 1,
            Self::Composite(composite) => {
                // Determine the maximum depth of the composite.
                let max_depth = composite.iter().map(|(_, private)| private.depth(counter)).fold(0, |a, b| a.max(b));
                // Add `1` to the depth of the member with the largest depth.
                max_depth.saturating_add(1)
            }
        }
    }

    /// Returns the identifiers that compose this private value.
    fn to_identifiers(&self) -> Vec<String> {
        match self {
            Self::Literal(..) => vec![],
            Self::Composite(composite) => composite.iter().flat_map(|(identifier, private)| {
                // Recursively get the identifiers of the member.
                let mut identifiers = vec![identifier.clone()];
                identifiers.extend(private.to_identifiers());
                identifiers
            }).collect(),
        }
    }

    /// Returns the field elements that compose this private value.
    fn to_fields(&self) -> Vec<N::Field> {
        match self {
            Self::Literal(_, literal) => (*literal).clone(),
            Self::Composite(composite) => composite.iter().flat_map(|(_, private)| private.to_fields()).collect(),
        }
    }

    /// Returns the number of field elements required to represent this private value.
    fn len(&self) -> usize {
        match self {
            Self::Literal(_, literal) => literal.len(),
            Self::Composite(composite) => composite.iter().map(|(_, private)| private.len()).sum(),
        }
    }
}
