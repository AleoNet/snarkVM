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

#![allow(clippy::module_inception)]
#![deny(unused_import_braces, unused_qualifications, trivial_casts, trivial_numeric_casts)]
#![deny(
    single_use_lifetimes,
    unused_qualifications,
    variant_size_differences,
    stable_features,
    unreachable_pub
)]
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
#![deny(
    const_err,
    unused_must_use,
    unused_mut,
    unused_unsafe,
    private_in_public,
    unsafe_code
)]
#![forbid(unsafe_code)]
#![cfg_attr(feature = "clippy", deny(warnings))]
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]
#![cfg_attr(feature = "clippy", allow(inline_always))]
#![cfg_attr(feature = "clippy", allow(too_many_arguments))]
#![cfg_attr(feature = "clippy", allow(unreadable_literal))]
#![cfg_attr(feature = "clippy", allow(many_single_char_names))]
#![cfg_attr(feature = "clippy", allow(new_without_default_derive))]

#[macro_use]
extern crate snarkvm_profiler;

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate thiserror;

pub mod account;
pub use account::*;

pub mod block;
pub use block::*;

pub mod circuits;
pub use circuits::*;

pub mod dpc;
pub use dpc::*;

pub mod errors;
pub use errors::*;

pub mod network;
pub use network::*;

pub mod posw;

pub mod program;
pub use program::*;

pub mod record;
pub use record::*;

pub mod state;
pub use state::*;

pub mod traits;
pub use traits::*;

pub mod transaction;
pub use transaction::*;

pub mod prelude {
    pub use crate::{
        account::*,
        block::*,
        circuits::*,
        dpc::*,
        errors::*,
        program::*,
        record::*,
        state::*,
        traits::*,
        transaction::*,
    };
}
