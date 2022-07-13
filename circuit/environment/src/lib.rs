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
#![allow(clippy::type_complexity)]

extern crate snarkvm_circuit_environment_witness;

pub use snarkvm_circuit_environment_witness::rename_selfs;

pub mod circuit;
pub use circuit::*;

pub mod environment;
pub use environment::*;

pub mod helpers;
pub use helpers::*;

pub mod macros;
pub use macros::*;

pub mod traits;
pub use traits::*;

pub mod prelude {
    pub use crate::{
        count,
        output_mode,
        rename_selfs,
        traits::*,
        witness,
        witness_mode,
        CircuitType,
        Count,
        Environment,
        LinearCombination,
        Mode,
        OutputMode,
        Variable,
    };
    pub use console::{
        prelude::{
            bail,
            ensure,
            fmt,
            has_duplicates,
            Debug,
            Display,
            Error,
            Formatter,
            FromStr,
            One as _,
            Result,
            Zero as _,
        },
        traits::{
            integers::{CheckedPow, IntegerProperties, IntegerType, Magnitude, WrappingDiv, WrappingPow, WrappingRem},
            string_parser,
            Double as _,
            FromBits as _,
            Inverse as _,
            Square as _,
            SquareRoot as _,
            ToBits as _,
        },
        Parser,
        ParserResult,
        TypeName,
    };
    pub use snarkvm_fields::{Field as _, PrimeField, Zero as _};
    pub use snarkvm_utilities::ToBits as _;

    #[cfg(debug_assertions)]
    pub use snarkvm_curves::AffineCurve as _;

    pub use core::ops::{
        Add,
        AddAssign,
        BitAnd,
        BitAndAssign,
        BitOr,
        BitOrAssign,
        BitXor,
        BitXorAssign,
        Deref,
        Div,
        DivAssign,
        Mul,
        MulAssign,
        Neg,
        Not,
        Shl,
        ShlAssign,
        Shr,
        ShrAssign,
        Sub,
        SubAssign,
    };
    pub use indexmap::IndexMap;
    pub use itertools::Itertools;
    pub use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{alpha1, alphanumeric1, char, one_of},
        combinator::{map, map_res, opt, recognize},
        multi::{many0, many1},
        sequence::{pair, terminated},
    };
    pub use num_traits::{Inv, One as NumOne, Pow, Unsigned};
    pub use once_cell::unsync::OnceCell;
}
