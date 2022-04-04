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

pub(super) mod annotation;
pub(super) use annotation::*;

pub mod identifier;
pub use identifier::*;

pub(super) mod literal_type;
pub(super) use literal_type::*;

pub(super) mod register;
pub(super) use register::*;

pub(super) mod sanitizer;
pub(super) use sanitizer::*;

pub mod value;
pub use value::*;

pub(super) mod variable_length;
