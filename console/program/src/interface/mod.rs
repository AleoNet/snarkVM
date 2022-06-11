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

mod bytes;
mod parse;

use crate::{Identifier, PlaintextType};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    has_duplicates,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Interface<N: Network> {
    /// The name of the interface.
    name: Identifier<N>,
    /// The name and type for the members of the interface.
    members: Vec<(Identifier<N>, PlaintextType<N>)>,
}

impl<N: Network> TypeName for Interface<N> {
    /// Returns the type name.
    fn type_name() -> &'static str {
        "interface"
    }
}
