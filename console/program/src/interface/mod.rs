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

mod literal_type;

use crate::{FromFields, ToFields};
use snarkvm_console_account::{Address, ViewKey};
use snarkvm_console_network::Network;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_utilities::{FromBits, ToBits};

use anyhow::{bail, Result};
use core::ops::Deref;

// /// An interface representing the layout for program data.
// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum Interface<N: Network> {}

// impl<N: Network> From<Vec<(Identifier<N>, Entry<N>)>> for Interface<N> {
//     /// Initializes a new `Data` value from a vector of `(Identifier, Entry)` pairs.
//     fn from(entries: Vec<(Identifier<N>, Entry<N>)>) -> Self {
//         Self(entries)
//     }
// }
