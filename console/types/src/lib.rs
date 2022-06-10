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

pub use snarkvm_console_network_environment as environment;

#[cfg(feature = "address")]
pub use snarkvm_console_types_address as address;
#[cfg(feature = "address")]
pub use snarkvm_console_types_address::Address;

#[cfg(feature = "boolean")]
pub use snarkvm_console_types_boolean as boolean;
#[cfg(feature = "boolean")]
pub use snarkvm_console_types_boolean::Boolean;

#[cfg(feature = "field")]
pub use snarkvm_console_types_field as field;
#[cfg(feature = "field")]
pub use snarkvm_console_types_field::Field;

#[cfg(feature = "group")]
pub use snarkvm_console_types_group as group;
#[cfg(feature = "group")]
pub use snarkvm_console_types_group::Group;

#[cfg(feature = "integers")]
pub use snarkvm_console_types_integers as integers;
#[cfg(feature = "integers")]
pub use snarkvm_console_types_integers::{I128, I16, I32, I64, I8, U128, U16, U32, U64, U8};

#[cfg(feature = "scalar")]
pub use snarkvm_console_types_scalar as scalar;
#[cfg(feature = "scalar")]
pub use snarkvm_console_types_scalar::Scalar;

#[cfg(feature = "string")]
pub use snarkvm_console_types_string as string;
#[cfg(feature = "string")]
pub use snarkvm_console_types_string::StringType;

pub mod prelude {
    pub use super::*;
    pub use snarkvm_console_network_environment::prelude::*;
}
