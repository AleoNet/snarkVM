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
#![allow(clippy::too_many_arguments)]

#[cfg(feature = "account")]
pub use snarkvm_console_account as account;

#[cfg(feature = "algorithms")]
pub use snarkvm_console_algorithms as algorithms;

#[cfg(feature = "collections")]
pub use snarkvm_console_collections as collections;

#[cfg(feature = "network")]
pub use snarkvm_console_network as network;

#[cfg(feature = "program")]
pub use snarkvm_console_program as program;

#[cfg(feature = "types")]
pub use snarkvm_console_types as types;

pub mod prelude {
    pub use crate::network::prelude::*;
}
