// Copyright (C) 2019-2021 Aleo Systems Inc.
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

#![deny(unused_import_braces)]
// #![deny(unused_mut, unused_qualifications, trivial_casts, trivial_numeric_casts, unreachable_pub)]
#![deny(variant_size_differences, stable_features)]
#![deny(
    non_shorthand_field_patterns,
    unused_attributes,
    unused_imports,
    unused_extern_crates
)]
#![deny(
    renamed_and_removed_lints,
    stable_features,
    unused_allocation,
    unused_comparisons,
    bare_trait_objects
)]
#![deny(const_err, unused_must_use, unused_unsafe, private_in_public, unsafe_code)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate thiserror;

pub mod algorithms;

pub mod curves;

pub mod fields;

pub mod errors;
pub use errors::*;

pub mod integers;

pub mod traits;
pub use traits::*;

pub mod utilities;
pub use utilities::*;
