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

#[macro_use]
extern crate num_derive;

extern crate core;
extern crate snarkvm_circuits_environment_witness;

pub use snarkvm_circuits_environment_witness::rename_selfs;

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
        rename_selfs,
        traits::*,
        witness,
        witness_mode,
        CircuitCount,
        Environment,
        LinearCombination,
        Mode,
        OutputMode,
        Variable,
    };
    pub use snarkvm_fields::{Field as F, One as O, PrimeField, Zero as Z};

    pub use core::{
        fmt::{self, Debug, Display},
        ops::{
            Add,
            AddAssign,
            BitAnd,
            BitAndAssign,
            BitOr,
            BitOrAssign,
            BitXor,
            BitXorAssign,
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
        },
    };
    pub use itertools::Itertools;
    pub use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{char, one_of},
        combinator::{map, map_res, opt, recognize},
        multi::{many0, many1},
        sequence::{pair, terminated},
    };
    pub use num_traits::{Inv, One as NumOne, Pow, Unsigned};
    pub use once_cell::unsync::OnceCell;
}
