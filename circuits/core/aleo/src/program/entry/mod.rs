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

use crate::{Aleo, Identifier, Literal};
use snarkvm_circuits_types::{Field, Mode, U8};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};

pub struct LiteralType<A: Aleo>(U8<A>);

pub trait EntryType<A: Aleo> {
    /// Returns the recursive depth of this entry.
    /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
    fn depth(&self, counter: usize) -> usize;
    /// Returns the identifiers that compose this entry.
    fn to_identifiers(&self) -> Vec<Identifier<A>>;
    /// Returns `true` if the entry is a literal.
    fn is_literal(&self) -> bool;
    /// Returns `true` if the entry is a composite.
    fn is_composite(&self) -> bool;
}

/// An entry stored in program data.
pub enum Entry<A: Aleo, Private: EntryType<A>> {
    /// A constant entry.
    Constant(Plaintext<A>),
    /// A publicly-visible entry.
    Public(Plaintext<A>),
    /// A private entry encrypted under the account owner's address.
    Private(Private),
}

impl<A: Aleo, Private: EntryType<A>> Entry<A, Private> {
    /// Returns the recursive depth of this entry.
    /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
    fn depth(&self) -> usize {
        match self {
            Self::Constant(constant) => constant.depth(0),
            Self::Public(public) => public.depth(0),
            Self::Private(private) => private.depth(0),
        }
    }

    /// Returns the identifiers that compose this entry.
    fn to_identifiers(&self) -> Vec<Identifier<A>> {
        match self {
            Self::Constant(constant) => constant.to_identifiers(),
            Self::Public(public) => public.to_identifiers(),
            Self::Private(private) => private.to_identifiers(),
        }
    }

    // /// If this entry is private, returns the field elements that compose the entry.
    // /// Otherwise, returns `None`.
    // fn to_fields(&self) -> Option<Vec<Field<A>>> {
    //     match self {
    //         Self::Constant(..) => None,
    //         Self::Public(..) => None,
    //         Self::Private(private) => Some(private.to_fields()),
    //     }
    // }

    /// Returns `true` if the entry is a literal.
    pub fn is_literal(&self) -> bool {
        match self {
            Self::Constant(constant) => constant.is_literal(),
            Self::Public(public) => public.is_literal(),
            Self::Private(private) => private.is_literal(),
        }
    }

    /// Returns `true` if the entry is a composite.
    pub fn is_composite(&self) -> bool {
        match self {
            Self::Constant(constant) => constant.is_composite(),
            Self::Public(public) => public.is_composite(),
            Self::Private(private) => private.is_composite(),
        }
    }

    /// Returns the mode of the entry.
    pub const fn mode(&self) -> Mode {
        match self {
            Self::Constant(..) => Mode::Constant,
            Self::Public(..) => Mode::Public,
            Self::Private(..) => Mode::Private,
        }
    }

    /// Returns `true` if the entry is constant.
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(..))
    }

    /// Returns `true` if the entry is public.
    pub const fn is_public(&self) -> bool {
        matches!(self, Self::Public(..))
    }

    /// Returns `true` if the entry is private.
    pub const fn is_private(&self) -> bool {
        matches!(self, Self::Private(..))
    }
}

pub enum Plaintext<A: Aleo> {
    /// A public literal.
    Literal(Literal<A>),
    /// A public composite.
    Composite(Vec<(Identifier<A>, Plaintext<A>)>),
}

impl<A: Aleo> EntryType<A> for Plaintext<A> {
    /// Returns the recursive depth of this public entry.
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

    /// Returns the identifiers that compose this public entry.
    fn to_identifiers(&self) -> Vec<Identifier<A>> {
        match self {
            Self::Literal(..) => vec![],
            Self::Composite(composite) => composite
                .iter()
                .flat_map(|(identifier, public)| {
                    // Recursively get the identifiers of the member.
                    let mut identifiers = vec![identifier.clone()];
                    identifiers.extend(public.to_identifiers());
                    identifiers
                })
                .collect(),
        }
    }

    /// Returns `true` if the entry is a literal.
    fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(..))
    }

    /// Returns `true` if the entry is a composite.
    fn is_composite(&self) -> bool {
        matches!(self, Self::Composite(..))
    }
}

pub enum Ciphertext<A: Aleo> {
    /// A private literal.
    Literal(LiteralType<A>, Vec<Field<A>>),
    /// A private composite.
    Composite(Vec<(Identifier<A>, Ciphertext<A>)>),
}

impl<A: Aleo> EntryType<A> for Ciphertext<A> {
    /// Returns the recursive depth of this private entry.
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

    /// Returns the identifiers that compose this private entry.
    fn to_identifiers(&self) -> Vec<Identifier<A>> {
        match self {
            Self::Literal(..) => vec![],
            Self::Composite(composite) => composite
                .iter()
                .flat_map(|(identifier, private)| {
                    // Recursively get the identifiers of the member.
                    let mut identifiers = vec![identifier.clone()];
                    identifiers.extend(private.to_identifiers());
                    identifiers
                })
                .collect(),
        }
    }

    /// Returns `true` if the entry is a literal.
    fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(..))
    }

    /// Returns `true` if the entry is a composite.
    fn is_composite(&self) -> bool {
        matches!(self, Self::Composite(..))
    }
}

impl<A: Aleo> Ciphertext<A> {
    /// Returns the field elements that compose this private entry.
    fn to_fields(&self) -> Vec<Field<A>> {
        match self {
            Self::Literal(_, literal) => (*literal).clone(),
            Self::Composite(composite) => composite.iter().flat_map(|(_, private)| private.to_fields()).collect(),
        }
    }

    /// Returns the number of field elements required to represent this private entry.
    fn len(&self) -> usize {
        match self {
            Self::Literal(_, literal) => literal.len(),
            Self::Composite(composite) => composite.iter().map(|(_, private)| private.len()).sum(),
        }
    }
}
