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

pub use snarkvm_circuit_environment as environment;
pub use snarkvm_circuit_types_address as address;
pub use snarkvm_circuit_types_boolean as boolean;
pub use snarkvm_circuit_types_field as field;
pub use snarkvm_circuit_types_group as group;
pub use snarkvm_circuit_types_integers as integers;
pub use snarkvm_circuit_types_scalar as scalar;
pub use snarkvm_circuit_types_string as string;

pub use address::Address;
pub use boolean::Boolean;
pub use environment::prelude::*;
pub use field::Field;
pub use group::Group;
pub use integers::{I128, I16, I32, I64, I8, U128, U16, U32, U64, U8};
pub use scalar::Scalar;
pub use string::StringType;

pub mod prelude {
    pub use super::*;
    pub use environment::prelude::*;
}
