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

pub mod inner_circuit;
pub use inner_circuit::*;

pub(crate) mod inner_private_variables;
pub(crate) use inner_private_variables::*;

pub(crate) mod inner_public_variables;
pub(crate) use inner_public_variables::*;

pub mod outer_circuit;
pub use outer_circuit::*;

pub(crate) mod outer_private_variables;
pub(crate) use outer_private_variables::*;

pub(crate) mod outer_public_variables;
pub(crate) use outer_public_variables::*;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod marlin_outer_snark_test;
