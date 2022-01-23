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

#![forbid(unsafe_code)]
#![allow(clippy::identity_op)]
#![allow(clippy::module_inception)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

pub mod address;
pub use address::*;

pub mod boolean;
pub use boolean::*;

pub mod fields;
pub use fields::*;

pub mod group;
pub use group::*;

pub mod helpers;

pub mod integers;
pub use integers::*;

// TODO (howardwu): This is temporary until the models interface is stabilized.
#[allow(unused)]
pub mod models;
pub use models::*;

// TODO (howardwu): This is temporary until the programs interface is stabilized.
#[allow(unused)]
pub mod programs;
pub use programs::*;

pub mod traits;
pub use traits::*;
