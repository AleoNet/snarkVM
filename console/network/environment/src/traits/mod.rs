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

mod arithmetic;
pub use arithmetic::*;

mod bitwise;
pub use bitwise::*;

mod from_field;
pub use from_field::*;

mod parse;
pub use parse::*;

mod string;
pub use string::string_parser;

mod to_field;
pub use to_field::*;

mod type_name;
pub use type_name::*;

mod types;
pub use types::*;

pub mod integers {
    pub use super::{
        integer_type::{CheckedPow, IntegerProperties, IntegerType, WrappingDiv, WrappingPow, WrappingRem},
        magnitude::Magnitude,
    };
}
