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

#[macro_use]
extern crate enum_index_derive;

// pub use snarkvm_circuits_core as core;
pub use snarkvm_circuits_core::{
    aleo::{Aleo, AleoV0, Literal},
    *,
};

pub use snarkvm_circuits_edge as edge;
pub use snarkvm_circuits_edge::*;

pub use snarkvm_circuits_environment as environment;
pub use snarkvm_circuits_environment::*;

pub use snarkvm_circuits_types as types;
pub use snarkvm_circuits_types::*;

// mod identifier;
// pub use identifier::*;

mod literal_type;
pub use literal_type::*;

mod primitive;
pub use primitive::*;

pub mod prelude {
    pub use super::*;
    pub use snarkvm_circuits_environment::*;
}
