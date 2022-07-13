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

mod assignment;
pub use assignment::Assignment;

pub mod circuit_type;
pub use circuit_type::*;

pub(crate) mod constraint;
pub(crate) use constraint::*;

pub(super) mod converter;

pub mod count;
pub use count::*;

pub(super) mod counter;
pub(super) use counter::*;

pub mod linear_combination;
pub use linear_combination::*;

mod mode;
pub use mode::*;

pub mod variable;
pub use variable::*;

pub(super) mod r1cs;
pub use r1cs::*;
