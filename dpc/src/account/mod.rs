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

pub mod account;
pub use account::*;

pub mod account_format;
pub use account_format::*;

pub mod address;
pub use address::*;

pub mod compute_key;
pub use compute_key::*;

pub mod private_key;
pub use private_key::*;

pub mod view_key;
pub use view_key::*;

#[cfg(test)]
pub mod tests;
