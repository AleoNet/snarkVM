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
#![allow(clippy::module_inception)]
#![allow(clippy::type_complexity)]

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate thiserror;

#[cfg(feature = "algorithms")]
pub mod algorithms;

pub mod bits;
pub use bits::*;

#[cfg(feature = "curves")]
pub mod curves;

pub mod errors;
pub use errors::*;

pub mod fields;
pub use fields::*;

pub mod integers;
pub use integers::*;

#[cfg(feature = "nonnative")]
pub mod nonnative;

pub mod traits;
pub use traits::*;

pub mod prelude {
    pub use crate::{bits::*, errors::*, fields::*, integers::*, traits::*};
}
