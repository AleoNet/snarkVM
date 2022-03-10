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

#![allow(clippy::module_inception)]
// #![cfg_attr(nightly, feature(doc_cfg, external_doc))]
// #![cfg_attr(nightly, warn(missing_docs))]
#![doc = include_str!("../documentation/the_aleo_curves/00_overview.md")]

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate thiserror;

pub mod bls12_377;

pub mod edwards_bls12;

pub mod edwards_bw6;

pub mod errors;
pub use errors::*;

pub mod templates;

#[cfg_attr(test, macro_use)]
pub mod traits;
pub use traits::*;
